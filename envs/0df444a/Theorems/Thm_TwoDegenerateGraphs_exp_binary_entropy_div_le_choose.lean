-- Prove2me | Theorems.Thm_TwoDegenerateGraphs_exp_binary_entropy_div_le_choose
-- name    : TwoDegenerateGraphs.exp_binary_entropy_div_le_choose
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:40.031605+00:00
-- url     : https://prove2.me/theorems/1c243348-77f8-4879-8140-ec3673db04ae
-- title:
--   TwoDegenerateGraphs.exp_binary_entropy_div_le_choose
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | CompactnessAndDegeneracy | external Lean 4.33.1 validation; bundle SHA256 86bc545d4a19897e327d6a4e4f158eea1a7dff6ffc50a29b8e2a28c393e047b3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology

theorem TwoDegenerateGraphs.exp_binary_entropy_div_le_choose
    (trialCount successCount : ℕ)
    (hcount : successCount ≤ trialCount) :
    Real.exp
        ((trialCount : ℝ) *
          Real.binEntropy
            ((successCount : ℝ) / (trialCount : ℝ))) /
        ((trialCount + 1 : ℕ) : ℝ) ≤
      (trialCount.choose successCount : ℝ) := by sorry
