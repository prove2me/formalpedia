-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_withoutReplacementBinaryPairMass_eq_pairTypeGroup
-- name    : TwoDegenerateGraphs.withoutReplacementBinaryPairMass_eq_pairTypeGroup
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:40.940432+00:00
-- url     : https://prove2.me/theorems/77f4f73a-112d-4e66-bf86-68e11317d5a2
-- title:
--   TwoDegenerateGraphs.withoutReplacementBinaryPairMass_eq_pairTypeGroup
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology

theorem TwoDegenerateGraphs.withoutReplacementBinaryPairMass_eq_pairTypeGroup
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (left right : Bool) :
    withoutReplacementBinaryPairMass parentCount
        (pairParentCoordinateOneCount parents coordinate) left right =
      ((pairTypeGroup parents coordinate
        (pairBitTypeOfOutcomes left right)).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
          (if left = right then (1 : ℝ) else 1 / 2) := by sorry
