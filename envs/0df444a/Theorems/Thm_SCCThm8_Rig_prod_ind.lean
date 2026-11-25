-- Prove2me | Theorems.Thm_SCCThm8_Rig_prod_ind
-- name    : SCCThm8.Rig.prod_ind
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:49:23.410929+00:00
-- url     : https://prove2.me/theorems/d1e87605-7d4c-4fab-9a1f-2535ddc842b0
-- title:
--   Rig: prod ind
-- statement:
--   The Rig construction uses the prod ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L311-L318
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L311-L318

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

theorem SCCThm8.Rig.prod_ind {H : Type*} [CommGroup H] (g' : Fin n → H) (S : Finset (Fin n)) :
    ∏ i, g' i ^ (if i ∈ S then (1 : ℤ) else 0) = ∏ i ∈ S, g' i := by sorry
