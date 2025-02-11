
#include "dyncfg.h"
#include "cfgwrapper.h"
#include "config.h"
#include "types.h"
#include "debug.h"

#include <jsoncpp/json/json.h>
#include <sys/time.h>
#include <map>




#define TRACE_MINI_VISITED(trace_mini, idx) (trace_mini[idx >> 3] & (1 << (idx & 7)))

// #include "afl-fuzz.h"

#ifdef __cplusplus
extern "C" {
#endif 


graph_cg_t cg_graph(0);

/* shared variable */
u32 pending_vulns, pending_canbe_reached;

u32 bug_freq_threshould = 0,       /* threshould for rare visited bug  */
    bit_freq_threshould = 0,       /* threshould for rare visited bits */
    current_max_bscore = 0;        /* Current max bug score found      */

extern u32  pending_not_fuzzed,        /* Queued but not done yet          */
            queued_paths;              /* Total number of queued testcases */

static u32 bitmap_freq[MAP_SIZE];
u8 low_freq_bits[MAP_SIZE];


std::uint32_t max_bug_distance = 0, min_bug_distance = UNREACHABLE_DIST;

std::map<u32, std::map<u32, u32>> func_dist_map;
u8 unvisited_func_map[FUNC_SIZE];
u32 *best_perf;

std::vector<u32> seed_length;



// #define PREFUZZ_DATA_INST

/* for max power limitation */
void add_to_vector(u32 length) {
  seed_length.push_back(length);
}
u32 get_pos_length(u32 pos) {
  sort(seed_length.begin(), seed_length.end());
  return seed_length[pos];
}


/* Get unix time in milliseconds */

static u64 get_cur_time(void) {

  struct timeval tv;
  struct timezone tz;

  gettimeofday(&tv, &tz);

  return (tv.tv_sec * 1000ULL) + (tv.tv_usec / 1000);

}

std::string get_format_time(void) {
  u64 exec_us = get_cur_time() - start_time;
  char fmt_time[11];
  sprintf(fmt_time, "[%02d:%02d:%02d]", 
          (u32)(exec_us / 1000 / 3600), 
          (u32)((exec_us / 1000 / 60) % 60), 
          (u32)((exec_us / 1000) % 60));
  return std::string(fmt_time);
}


void initialized_callgraph() {
  std::string temporary_dir = std::getenv("TMP_DIR");
  std::string runtime_dir = temporary_dir + "/runtimes/";

  load_cg_file(runtime_dir + "/callgraph.dot", cg_graph);
  for (auto src : boost::make_iterator_range(vertices(cg_graph))) {
    std::string cfg_name = runtime_dir + "/cfg." + cg_graph[src].name + ".dot";
    if (if_cfg_exists(cfg_name))
      load_cfg_file(cfg_name, cg_graph[src].cfg);
    else 
      cg_graph[src].node_id = 0;
      // load_cfg_file(cfg_name, cg_graph[src].cfg);
      
  }

}


void initialized_bug_map() {

  std::string temporary_dir = std::getenv("TMP_DIR");
  std::map<std::string, u32> func2id;
  std::ifstream fi(temporary_dir + "/funcid.csv");
  if (fi.is_open()) {
    std::string line;
    while (getline(fi, line)) {
      
      std::size_t dis_pos = line.find(",");
      std::string fname = line.substr(dis_pos + 1, line.length() - dis_pos);
      std::string idx_str = line.substr(0, dis_pos);
      func2id.emplace(fname, atoi(idx_str.c_str()));
      // std::cout << fname << " : " << idx_str << "\n";
    }
  }

  /* initialized vuln functions */
  std::ifstream bfunc(temporary_dir + "/vulnfunc.csv", std::ifstream::binary);
  if (bfunc.is_open()) {
    std::string line;
    while (getline(bfunc, line)) {
      auto biter = func2id.find(line);
      if (biter != func2id.end()) {
        unvisited_func_map[biter->second] = 1;
      }
      // else PFATAL("Failed found func %s.", line.c_str());
    }
  }
  return;
}


void initialized_dist_map() {
  Json::Value shortest_dist_map;
  Json::Reader reader;
  std::string temporary_dir = std::getenv("TMP_DIR"), errs;
  std::ifstream dist_map(temporary_dir + "/runtimes/calldst.json", std::ifstream::binary);
  
  if (!reader.parse(dist_map, shortest_dist_map, false))
    PFATAL("Failed loading dist map !");

  for (auto dst_s : shortest_dist_map.getMemberNames()) {
    std::map<u32, u32> func_shortest;
    Json::Value func_shortest_value = shortest_dist_map[dst_s];
    for (auto src_s : func_shortest_value.getMemberNames()) {
      func_shortest.insert(std::make_pair(std::stoi(src_s), func_shortest_value[src_s].asInt()));
    }
    func_dist_map.insert(std::make_pair(std::stoi(dst_s), func_shortest));
  }

}




void ranking_targets(u32* reach_bits_count, u32* trigger_bits_count) {

  std::vector<std::uint32_t> reached_bugs;
  std::uint32_t max_value = 1;

  for (u32 i = 0; i < VMAP_COUNT; i ++) {
    if (reach_bits_count[i] && !trigger_bits_count[i]) {
      reached_bugs.push_back(reach_bits_count[i]);
      if (max_value < reach_bits_count[i]) max_value = reach_bits_count[i];
    }
  }
  std::sort(reached_bugs.begin(), reached_bugs.end());
  if (max_value != 1) {
    float rate = pending_not_fuzzed / queued_paths;
    // if (rate < 0.2) rate = 0.2;
    // if (rate > 0.5) rate = 0.5;
    if (rate < 0.2) rate = 0.2;
    else if (rate < 0.5) rate = 0.15;
    else rate = 0.1;
    bug_freq_threshould = reached_bugs[reached_bugs.size() * rate];
  }
  std::vector<std::uint32_t>().swap(reached_bugs);

}



void update_unvisited_bfunc(u8 *virgin_func) {
  for (int i = 0; i < FUNC_SIZE; i ++) {
    if (virgin_func[i]) unvisited_func_map[i] = 0;
  }
}

void update_exp_scoring(struct queue_entry **top_rated_func,
                        struct queue_entry* queue) {

  char log_path[128];
  snprintf(log_path, sizeof(log_path), "/box/output/update_exp_scoring.log");
  FILE *log_file = fopen(log_path, "a");
  if (!log_file) {
    perror("Failed to open log file");
    return;
  }

  if (!best_perf) {
    best_perf = (u32 *)malloc(sizeof(u32) * FUNC_SIZE);
    memset(best_perf, 255, FUNC_SIZE * sizeof(u32));
  }

  for (u32 i = 0; i < FUNC_SIZE; i++) {

    if (!unvisited_func_map[i]) {
      continue;
    } else {
      fprintf(log_file, "%u/unvisited_func_map\n", i);
    }
    // iterate over queue to find a seed with shortest distance

    if (top_rated_func[i] && top_rated_func[i]->was_fuzzed) {
      fprintf(log_file, "%u/top_rated_func[i]->was_fuzzed/%s\n", i, top_rated_func[i]->fname);
      top_rated_func[i] = NULL;
    }

    u32 seeds_checked = 0, valid_seeds = 0;
    for (struct queue_entry *q = queue; q; q = q->next) {
      seeds_checked++;
      // skip fuzzed seed
      if (q->was_fuzzed) continue;
      u32 fexp_score = 0, shortest_dist = UNREACHABLE_DIST;
      for (auto iter = func_dist_map[i].begin(); iter != func_dist_map[i].end(); iter++) {
        if (q->trace_func[iter->first] && iter->second < shortest_dist) {
          shortest_dist = iter->second;
        }
      }
      if (shortest_dist != UNREACHABLE_DIST) fexp_score = shortest_dist * 100;

      if (fexp_score) {
        valid_seeds++;
        if (!top_rated_func[i]) {
          fprintf(log_file, "[Update best seed] %u/first seed %s(%u,%llu,%u)\n",
                  i,
                  (const char*)q->fname,
                  fexp_score,
                  q->exec_us,
                  q->len);
          top_rated_func[i] = q;
          best_perf[i] = fexp_score;
        } else if (fexp_score < best_perf[i] ||
            (fexp_score == best_perf[i] &&
             q->exec_us * q->len < top_rated_func[i]->exec_us * top_rated_func[i]->len)) {
          fprintf(log_file, "[Update best seed] %u/from %s(%u,%llu,%u)/to %s(%u,%llu,%u)\n",
                  i,
                  (const char*)top_rated_func[i]->fname,
                  best_perf[i],
                  top_rated_func[i]->exec_us,
                  top_rated_func[i]->len,
                  (const char*)q->fname,
                  fexp_score,
                  q->exec_us,
                  q->len);
          top_rated_func[i] = q;
          best_perf[i] = fexp_score;
        }
      }

    }

    if (top_rated_func[i]) {
      fprintf(log_file, "[Result] %u/%s(Total %u, Valid %u, Score %u)\n",
        i,
        (const char*)top_rated_func[i]->fname,
        seeds_checked,
        valid_seeds,
        best_perf[i]);
    }
  }

  fclose(log_file);
}

void update_bug_scoring(u32* reach_bits_count, u32* trigger_bits_count) {
  /* update each bug's score according to visit freq */
  ranking_targets(reach_bits_count, trigger_bits_count);

}




#ifdef __cplusplus
};
#endif 