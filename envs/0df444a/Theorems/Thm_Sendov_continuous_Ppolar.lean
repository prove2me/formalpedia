-- Prove2me | Theorems.Thm_Sendov_continuous_Ppolar
-- name    : Sendov.continuous_Ppolar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:43:11.839377+00:00
-- url     : https://prove2.me/theorems/0ae608a4-4569-5c26-843c-c61f291586cb
-- title:
--   Sendov: continuous Ppolar
-- statement:
--   The Sendov construction uses the continuous Ppolar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Setup.lean#L54-L55
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Reduction/Setup.lean#L54-L55

import Definitions.Def_Sendov_Common_Chord
import Definitions.Def_Sendov_Reduction_Setup
set_option autoImplicit false
open Sendov
variable {n : ℕ} {a x t α : ℝ}

theorem Sendov.continuous_Ppolar (a x : ℝ) : Continuous fun t : ℝ => Ppolar a x t := by sorry
