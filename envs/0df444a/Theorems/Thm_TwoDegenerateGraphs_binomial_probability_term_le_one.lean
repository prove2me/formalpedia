-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_binomial_probability_term_le_one
-- name    : TwoDegenerateGraphs.binomial_probability_term_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:40.031605+00:00
-- url     : https://prove2.me/theorems/f7c63935-1b7c-43b1-a891-ec352d0fe4dd
-- title:
--   TwoDegenerateGraphs.binomial_probability_term_le_one
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology

theorem TwoDegenerateGraphs.binomial_probability_term_le_one
    (trialCount successCount : ℕ) (probability : ℝ)
    (hcount : successCount ≤ trialCount)
    (hprobability_zero : 0 ≤ probability)
    (hprobability_one : probability ≤ 1) :
    (trialCount.choose successCount : ℝ) *
        probability ^ successCount *
        (1 - probability) ^ (trialCount - successCount) ≤ 1 := by sorry
