-- Prove2me | Theorems.Thm_Sendov_derivative_rotate
-- name    : Sendov.derivative_rotate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T20:06:22.349054+00:00
-- url     : https://prove2.me/theorems/a4f4120b-71b0-45c4-8059-4d7e23d4c60c
-- title:
--   Sendov: derivative rotate
-- statement:
--   The Sendov construction uses the derivative rotate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Conjecture.lean#L53-L56
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Conjecture.lean#L53-L56

import Definitions.Def_Sendov_Interior
import Definitions.Def_Sendov_Boundary
import Definitions.Def_Sendov_Conjecture
set_option autoImplicit false
open Sendov
open Polynomial

theorem Sendov.derivative_rotate (ω : ℂ) (p : ℂ[X]) :
    derivative (rotate ω p) = C ω * rotate ω (derivative p) := by sorry
