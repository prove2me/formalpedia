-- Prove2me | Theorems.Thm_Sendov_alpha_le_half
-- name    : Sendov.alpha_le_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:44:43.032472+00:00
-- url     : https://prove2.me/theorems/ec2e960b-7e2e-5e12-a081-ca980eeb073b
-- title:
--   Sendov: alpha le half
-- statement:
--   The Sendov construction uses the alpha le half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Setup.lean#L71-L75
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Setup.lean#L71-L75

import Definitions.Def_Sendov_Common_Chord
import Definitions.Def_Sendov_Reduction_Setup
set_option autoImplicit false
open Sendov
variable {n : ℕ} {a x t α : ℝ}

theorem Sendov.alpha_le_half (hn : 2 ≤ n) (hα : α = M n * (1 - a ^ 2) / 2) :
    α ≤ M n / 2 := by sorry
