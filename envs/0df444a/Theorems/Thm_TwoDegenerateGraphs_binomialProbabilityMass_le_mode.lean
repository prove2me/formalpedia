-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_binomialProbabilityMass_le_mode
-- name    : TwoDegenerateGraphs.binomialProbabilityMass_le_mode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:40.031605+00:00
-- url     : https://prove2.me/theorems/0734fb71-8cb1-461e-9a6d-81c9a479ac9f
-- title:
--   TwoDegenerateGraphs.binomialProbabilityMass_le_mode
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology

theorem TwoDegenerateGraphs.binomialProbabilityMass_le_mode
    (trialCount mode successCount : ℕ)
    (hmode : mode ≤ trialCount)
    (hsuccess : successCount ≤ trialCount) :
    binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) ≤
      binomialProbabilityMass trialCount mode
        ((mode : ℝ) / (trialCount : ℝ)) := by sorry
