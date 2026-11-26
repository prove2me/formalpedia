-- Prove2me | Theorems.Thm_QuadraticFloor_negOnePow_ediv_add_mul
-- name    : QuadraticFloor.negOnePow_ediv_add_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:53:55.864848+00:00
-- url     : https://prove2.me/theorems/551d32fe-c5b8-5080-86ff-7c574f81c923
-- title:
--   Quadratic Floor: neg One Pow ediv add mul
-- statement:
--   The Quadratic Floor construction uses the neg One Pow ediv add mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L244-L246
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L244-L246

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp

theorem QuadraticFloor.negOnePow_ediv_add_mul (v : ℤ) (k : ℤ) (hp0 : (p : ℤ) ≠ 0) :
    (((v + p * k) / (p : ℤ)).negOnePow : ℤ) = ((v / p).negOnePow : ℤ) * (k.negOnePow : ℤ) := by sorry
