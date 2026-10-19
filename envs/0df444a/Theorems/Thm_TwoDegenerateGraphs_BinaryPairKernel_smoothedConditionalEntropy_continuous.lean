-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_BinaryPairKernel_smoothedConditionalEntropy_continuous
-- name    : TwoDegenerateGraphs.BinaryPairKernel.smoothedConditionalEntropy_continuous
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:40.031605+00:00
-- url     : https://prove2.me/theorems/ab606026-4943-401d-a3aa-eb7da606eee9
-- title:
--   TwoDegenerateGraphs.BinaryPairKernel.smoothedConditionalEntropy_continuous
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open TwoDegenerateGraphs.BinaryPairKernel

theorem TwoDegenerateGraphs.BinaryPairKernel.smoothedConditionalEntropy_continuous (kernel : BinaryPairKernel) :
    Continuous (smoothedConditionalEntropy kernel) := by sorry
