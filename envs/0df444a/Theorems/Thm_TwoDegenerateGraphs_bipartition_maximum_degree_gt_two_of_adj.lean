-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_bipartition_maximum_degree_gt_two_of_adj
-- name    : TwoDegenerateGraphs.bipartition_maximum_degree_gt_two_of_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:40.940432+00:00
-- url     : https://prove2.me/theorems/3362cdb7-ceda-4235-85c9-f906c3cf4409
-- title:
--   TwoDegenerateGraphs.bipartition_maximum_degree_gt_two_of_adj
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open Classical

theorem TwoDegenerateGraphs.bipartition_maximum_degree_gt_two_of_adj
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) {u v : V}
    (hadj : G.Adj u v)
    (hu : 2 < G.degree u) (hv : 2 < G.degree v) :
    ∀ coloring : G.Coloring (Fin 2), ∀ side : Fin 2,
      2 < (Finset.univ.filter
        (fun vertex : V => coloring vertex = side)).sup
        (fun vertex => G.degree vertex) := by sorry
