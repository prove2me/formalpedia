-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_BinaryPairKernel_bitDisagreementProbability_mem_Icc
-- name    : TwoDegenerateGraphs.BinaryPairKernel.bitDisagreementProbability_mem_Icc
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:40.031605+00:00
-- url     : https://prove2.me/theorems/262d16c8-46b5-45bc-b192-f2e5be674634
-- title:
--   TwoDegenerateGraphs.BinaryPairKernel.bitDisagreementProbability_mem_Icc
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
open TwoDegenerateGraphs.BinaryPairKernel

theorem TwoDegenerateGraphs.BinaryPairKernel.bitDisagreementProbability_mem_Icc (parent : Bool)
    (childProbability : ℝ)
    (hzero : 0 ≤ childProbability) (hone : childProbability ≤ 1) :
    0 ≤ bitDisagreementProbability parent childProbability ∧
      bitDisagreementProbability parent childProbability ≤ 1 := by sorry
