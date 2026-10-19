-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_hammingRetentionMeasure_real_pairChildren
-- name    : TwoDegenerateGraphs.hammingRetentionMeasure_real_pairChildren
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:42.805702+00:00
-- url     : https://prove2.me/theorems/4a8f6fe3-09e8-47a6-b508-4197a9e27bf5
-- title:
--   TwoDegenerateGraphs.hammingRetentionMeasure_real_pairChildren
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology

theorem TwoDegenerateGraphs.hammingRetentionMeasure_real_pairChildren
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : PairLayer parentCount 1 → HammingWord dimension)
    (hinjective : Function.Injective children) :
    (hammingRetentionMeasure dimension).real
        (pairChildRetentionEvent side children) =
      hammingRetentionProbability dimension ^ (parentCount.choose 2) := by sorry
