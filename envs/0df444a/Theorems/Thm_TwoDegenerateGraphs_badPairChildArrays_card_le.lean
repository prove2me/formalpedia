-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_badPairChildArrays_card_le
-- name    : TwoDegenerateGraphs.badPairChildArrays_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:41.731406+00:00
-- url     : https://prove2.me/theorems/27e36f41-efb2-45f0-adc0-085ba90ae45b
-- title:
--   TwoDegenerateGraphs.badPairChildArrays_card_le
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology

theorem TwoDegenerateGraphs.badPairChildArrays_card_le
    {parentCount dimension : ℕ}
    (hparents : 2 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (threshold : ℝ) :
    ((badPairChildArrays parents threshold).card : ℝ) ≤
      (((parentCount.choose 2 + 1) ^ (3 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 2 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold) := by sorry
