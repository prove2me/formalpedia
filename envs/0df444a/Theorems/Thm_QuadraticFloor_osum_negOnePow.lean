-- Prove2me | Theorems.Thm_QuadraticFloor_osum_negOnePow
-- name    : QuadraticFloor.osum_negOnePow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:53:31.645603+00:00
-- url     : https://prove2.me/theorems/d5391626-8541-47d2-8283-c267cc5c9161
-- title:
--   Quadratic Floor: osum neg One Pow
-- statement:
--   The Quadratic Floor construction uses the osum neg One Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L67-L76
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L67-L76

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset

theorem QuadraticFloor.osum_negOnePow (t : ℤ) : 2 * osum t (fun j => (j.negOnePow : ℤ)) = 1 - (t.negOnePow : ℤ) := by sorry
