-- Prove2me | Theorems.Thm_Sendov_eval_derivative_rotate
-- name    : Sendov.eval_derivative_rotate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T20:06:30.686668+00:00
-- url     : https://prove2.me/theorems/63ed24f4-051a-494c-9f7d-aee949996d4d
-- title:
--   Sendov: eval derivative rotate
-- statement:
--   The Sendov construction uses the eval derivative rotate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Conjecture.lean#L58-L60
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Conjecture.lean#L58-L60

import Definitions.Def_Sendov_Interior
import Definitions.Def_Sendov_Boundary
import Definitions.Def_Sendov_Conjecture
set_option autoImplicit false
open Sendov
open Polynomial

theorem Sendov.eval_derivative_rotate (ω : ℂ) (p : ℂ[X]) (x : ℂ) :
    (derivative (rotate ω p)).eval x = ω * (derivative p).eval (ω * x) := by sorry
