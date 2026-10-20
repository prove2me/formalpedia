-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_pairTypeGroup_probability_mul_childRatio
-- name    : TwoDegenerateGraphs.pairTypeGroup_probability_mul_childRatio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:40.940432+00:00
-- url     : https://prove2.me/theorems/026c321d-160e-45ac-afa0-1f692488ab1a
-- title:
--   TwoDegenerateGraphs.pairTypeGroup_probability_mul_childRatio
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology

theorem TwoDegenerateGraphs.pairTypeGroup_probability_mul_childRatio
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : PairBitType) :
    ((pairTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 2 : ℝ) *
      (((pairTypeGroupChildOnes parents children
          coordinate bitType).card : ℝ) /
        ((pairTypeGroup parents coordinate bitType).card : ℝ)) =
      ((pairTypeGroupChildOnes parents children
        coordinate bitType).card : ℝ) /
          (parentCount.choose 2 : ℝ) := by sorry
