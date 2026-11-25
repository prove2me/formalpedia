-- Prove2me | Theorems.Thm_SCCThm8_Rig_prod_sw
-- name    : SCCThm8.Rig.prod_sw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:49:08.561014+00:00
-- url     : https://prove2.me/theorems/74cf17fb-b059-478d-8b2e-6c7e4a23db3f
-- title:
--   Rig: prod sw
-- statement:
--   The Rig construction uses the prod sw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L298-L303
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L298-L303

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.Rig
variable {n : ℕ}

theorem SCCThm8.Rig.prod_sw {H : Type*} [CommGroup H] (g' : Fin n → H) {A : Finset (Fin n)} {i j : Fin n}
    (hi : i ∈ A) (hj : j ∉ A) :
    ∏ x ∈ sw A i j, g' x = g' j * (g' i)⁻¹ * ∏ x ∈ A, g' x := by sorry
