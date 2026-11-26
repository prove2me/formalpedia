-- Prove2me | Theorems.Thm_QuadraticFloor_ediv_small
-- name    : QuadraticFloor.ediv_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T00:54:08.067168+00:00
-- url     : https://prove2.me/theorems/e80d16c0-2c04-5674-9ba9-bd6b64182d58
-- title:
--   Quadratic Floor: ediv small
-- statement:
--   The Quadratic Floor construction uses the ediv small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L326-L341
-- source:
--   https://github.com/jkfarland-bot/QuadraticFloor/blob/7e51a19db5a27cf064bf5d2f8845812fe1070077/QuadraticFloor/Monic.lean#L326-L341

module
public import Definitions.Def_QuadraticFloor_Corollaries
public import Definitions.Def_QuadraticFloor_Monic
set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem QuadraticFloor.ediv_small {v : ℤ} {P : ℤ} (hP : |v| < P) :
    v / P = if v < 0 then -1 else 0 := by sorry
