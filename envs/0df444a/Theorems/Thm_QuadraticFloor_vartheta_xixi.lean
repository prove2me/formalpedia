-- Prove2me | Theorems.Thm_QuadraticFloor_vartheta_xixi
-- name    : QuadraticFloor.vartheta_xixi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:52:24.079938+00:00
-- url     : https://prove2.me/theorems/bfe34c3c-012f-568d-a57f-772a674cf92d
-- title:
--   Quadratic Floor: vartheta xixi
-- statement:
--   The Quadratic Floor construction uses the vartheta xixi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L174-L179
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/CoefficientFive.lean#L174-L179

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_CoefficientFive
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp

theorem QuadraticFloor.vartheta_xixi : vartheta p (xi * xi) = fun x => (eta p x : ℂ) * (jacobiSym x 5 : ℂ) := by sorry
