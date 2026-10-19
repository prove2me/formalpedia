-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_binomialProbabilityMass_mode_ge_inverse
-- name    : TwoDegenerateGraphs.binomialProbabilityMass_mode_ge_inverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:40.031605+00:00
-- url     : https://prove2.me/theorems/bccc907a-4a36-4404-b226-55d22456f883
-- title:
--   TwoDegenerateGraphs.binomialProbabilityMass_mode_ge_inverse
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology

theorem TwoDegenerateGraphs.binomialProbabilityMass_mode_ge_inverse
    (trialCount mode : ℕ) (hmode : mode ≤ trialCount) :
    1 / ((trialCount + 1 : ℕ) : ℝ) ≤
      binomialProbabilityMass trialCount mode
        ((mode : ℝ) / (trialCount : ℝ)) := by sorry
