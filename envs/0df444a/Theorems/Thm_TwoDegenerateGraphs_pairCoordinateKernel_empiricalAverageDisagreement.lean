-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_pairCoordinateKernel_empiricalAverageDisagreement
-- name    : TwoDegenerateGraphs.pairCoordinateKernel_empiricalAverageDisagreement
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:41.731406+00:00
-- url     : https://prove2.me/theorems/df9c410c-d91b-454b-97b3-2dc99bbe4fc3
-- title:
--   TwoDegenerateGraphs.pairCoordinateKernel_empiricalAverageDisagreement
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology

theorem TwoDegenerateGraphs.pairCoordinateKernel_empiricalAverageDisagreement
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    empiricalAverageDisagreement parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (pairCoordinateKernel (by omega) parents children coordinate) =
      (((pairTypeGroupChildOnes parents children coordinate 0).card : ℝ) +
        ((pairTypeGroup parents coordinate 2).card : ℝ) / 2 +
        (((pairTypeGroup parents coordinate 1).card : ℝ) -
          ((pairTypeGroupChildOnes parents children coordinate 1).card : ℝ))) /
        (parentCount.choose 2 : ℝ) := by sorry
