-- Prove2me | Theorems.Thm_Sendov_pev_intCast
-- name    : Sendov.pev_intCast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:02.032169+00:00
-- url     : https://prove2.me/theorems/4168286f-85fa-56a9-af1b-e7e731fa196f
-- title:
--   Sendov: pev int Cast
-- statement:
--   Evaluating a coefficient polynomial over `ℝ` at an integer point is the packed
--   evaluation over `ℤ`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L50-L56
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/PackBridge.lean#L50-L56

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge
set_option autoImplicit false
open Sendov

theorem Sendov.pev_intCast (p : List ℤ) (b : ℤ) : pev p (b : ℝ) = (pevZ p b : ℝ) := by sorry
