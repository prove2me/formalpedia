-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_hammingWordEdge_sum_const
-- name    : TwoDegenerateGraphs.hammingWordEdge_sum_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:42.805702+00:00
-- url     : https://prove2.me/theorems/58657eda-42c0-44fc-9699-76cb0bb4a3a0
-- title:
--   TwoDegenerateGraphs.hammingWordEdge_sum_const
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
attribute [local instance] Classical.propDecidable

theorem TwoDegenerateGraphs.hammingWordEdge_sum_const
    (dimension radius : ℕ) (weight : ℝ) :
    (∑ left : HammingWord dimension,
      ∑ right : HammingWord dimension,
        if hammingDist left right ≤ radius then weight else 0) =
      ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) * weight := by sorry
