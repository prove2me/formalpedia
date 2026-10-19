-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_pairGraphOverFin_bipartition_maximum_degree_gt_two
-- name    : TwoDegenerateGraphs.pairGraphOverFin_bipartition_maximum_degree_gt_two
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:40.940432+00:00
-- url     : https://prove2.me/theorems/f52df99d-bfcc-4cac-8416-09dfe69b2492
-- title:
--   TwoDegenerateGraphs.pairGraphOverFin_bipartition_maximum_degree_gt_two
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open Classical

theorem TwoDegenerateGraphs.pairGraphOverFin_bipartition_maximum_degree_gt_two
    (baseSize depth : ℕ) (hbase : 4 ≤ baseSize) (hdepth : 2 ≤ depth) :
    ∀ coloring : (pairGraphOverFin baseSize depth).Coloring (Fin 2),
      ∀ side : Fin 2,
        2 < (Finset.univ.filter
          (fun vertex : Fin (Fintype.card (PairVertex baseSize depth)) =>
            coloring vertex = side)).sup
          (fun vertex => (pairGraphOverFin baseSize depth).degree vertex) := by sorry
