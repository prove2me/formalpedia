-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_pairGraph_exists_adj_degree_gt_two
-- name    : TwoDegenerateGraphs.pairGraph_exists_adj_degree_gt_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:40.940432+00:00
-- url     : https://prove2.me/theorems/118105ae-f6e9-48f8-b2f5-b87804fcffbf
-- title:
--   TwoDegenerateGraphs.pairGraph_exists_adj_degree_gt_two
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open Classical

theorem TwoDegenerateGraphs.pairGraph_exists_adj_degree_gt_two
    (baseSize depth : ℕ) (hbase : 4 ≤ baseSize) (hdepth : 2 ≤ depth) :
    ∃ u v : PairVertex baseSize depth,
      (pairParentSystem baseSize depth).graph.Adj u v ∧
      2 < (pairParentSystem baseSize depth).graph.degree u ∧
      2 < (pairParentSystem baseSize depth).graph.degree v := by sorry
