-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_sum_pairCoordinatePairMismatchCount
-- name    : TwoDegenerateGraphs.sum_pairCoordinatePairMismatchCount
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:41.731406+00:00
-- url     : https://prove2.me/theorems/f6b94f6d-ddff-4d7c-9232-7f67e14cd52a
-- title:
--   TwoDegenerateGraphs.sum_pairCoordinatePairMismatchCount
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology

theorem TwoDegenerateGraphs.sum_pairCoordinatePairMismatchCount
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ pair : PairLayer parentCount 1,
      pairCoordinatePairMismatchCount
        parents children coordinate pair) =
      2 * (pairTypeGroupChildOnes parents children coordinate 0).card +
      (pairTypeGroup parents coordinate 2).card +
      2 *
        ((pairTypeGroup parents coordinate 1).card -
          (pairTypeGroupChildOnes parents children coordinate 1).card) := by sorry
