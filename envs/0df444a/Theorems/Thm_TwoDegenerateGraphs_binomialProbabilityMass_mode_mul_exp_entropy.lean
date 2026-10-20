-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_binomialProbabilityMass_mode_mul_exp_entropy
-- name    : TwoDegenerateGraphs.binomialProbabilityMass_mode_mul_exp_entropy
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:40.031605+00:00
-- url     : https://prove2.me/theorems/3a42eb3c-3170-446d-9892-a9a669a663f3
-- title:
--   TwoDegenerateGraphs.binomialProbabilityMass_mode_mul_exp_entropy
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology

theorem TwoDegenerateGraphs.binomialProbabilityMass_mode_mul_exp_entropy
    (trialCount mode : ℕ) (hmode : mode ≤ trialCount) :
    binomialProbabilityMass trialCount mode
        ((mode : ℝ) / (trialCount : ℝ)) *
      Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy ((mode : ℝ) / (trialCount : ℝ))) =
      (trialCount.choose mode : ℝ) := by sorry
