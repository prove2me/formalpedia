-- Prove2me | Theorems.Thm_Sendov_eval_rotate
-- name    : Sendov.eval_rotate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T20:05:42.191508+00:00
-- url     : https://prove2.me/theorems/08027e39-1c1c-5aa7-956f-a2cd67fc9ae8
-- title:
--   Sendov: eval rotate
-- statement:
--   The Sendov construction uses the eval rotate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Conjecture.lean#L45-L47
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Conjecture.lean#L45-L47

import Definitions.Def_Sendov_Interior
import Definitions.Def_Sendov_Boundary
import Definitions.Def_Sendov_Conjecture
set_option autoImplicit false
open Sendov
open Polynomial

theorem Sendov.eval_rotate (ω : ℂ) (p : ℂ[X]) (x : ℂ) :
    (rotate ω p).eval x = p.eval (ω * x) := by sorry
