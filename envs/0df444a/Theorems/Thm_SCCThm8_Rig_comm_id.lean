-- Prove2me | Theorems.Thm_SCCThm8_Rig_comm_id
-- name    : SCCThm8.Rig.comm_id
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:49:04.697184+00:00
-- url     : https://prove2.me/theorems/8ec332f9-e426-5b26-8995-669ef1fab9e2
-- title:
--   Rig: comm id
-- statement:
--   The Rig construction uses the comm id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L305-L309
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L305-L309

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

theorem SCCThm8.Rig.comm_id {H : Type*} [CommGroup H] (a b c d e : H) :
    a * b⁻¹ * c⁻¹ * d = a * e * d * (b * e * c)⁻¹ := by sorry
