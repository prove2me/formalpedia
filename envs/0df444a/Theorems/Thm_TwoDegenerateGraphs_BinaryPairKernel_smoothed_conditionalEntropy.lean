-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_BinaryPairKernel_smoothed_conditionalEntropy
-- name    : TwoDegenerateGraphs.BinaryPairKernel.smoothed_conditionalEntropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:40.031605+00:00
-- url     : https://prove2.me/theorems/ecd88325-5574-43c2-9af9-d75b8ce874d9
-- title:
--   TwoDegenerateGraphs.BinaryPairKernel.smoothed_conditionalEntropy
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open TwoDegenerateGraphs.BinaryPairKernel

theorem TwoDegenerateGraphs.BinaryPairKernel.smoothed_conditionalEntropy (kernel : BinaryPairKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing)
    (hmixing_one : mixing ≤ 1) :
    (smoothed kernel mixing hmixing_zero hmixing_one).conditionalEntropy =
      smoothedConditionalEntropy kernel mixing := by sorry
