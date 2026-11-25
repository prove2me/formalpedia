-- Prove2me | Theorems.Thm_SCCThm8_PRig_prodP_update
-- name    : SCCThm8.PRig.prodP_update
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:52:54.023404+00:00
-- url     : https://prove2.me/theorems/889fd164-a3c6-5801-b6c4-4ebd87153a66
-- title:
--   PRig: prod P update
-- statement:
--   The PRig construction uses the prod P update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerRigidity.lean#L61-L74
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerRigidity.lean#L61-L74

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_PowerRigidity
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.PRig
open Rig Function

theorem SCCThm8.PRig.prodP_update {n m : ℕ} {H : Type*} [CommGroup H] (g' : Fin m → Fin n → H)
    (A : Fin m → Finset (Fin n)) (j : Fin m) (Y : Finset (Fin n)) :
    ∏ j', ∏ x ∈ update A j Y j', g' j' x =
      (∏ x ∈ Y, g' j x) * (∏ x ∈ A j, g' j x)⁻¹ * ∏ j', ∏ x ∈ A j', g' j' x := by sorry
