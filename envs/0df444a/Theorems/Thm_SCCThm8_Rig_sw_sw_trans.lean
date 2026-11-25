-- Prove2me | Theorems.Thm_SCCThm8_Rig_sw_sw_trans
-- name    : SCCThm8.Rig.sw_sw_trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:49:37.6861+00:00
-- url     : https://prove2.me/theorems/a36104c8-110a-4b3b-91f9-0b15d52cad2a
-- title:
--   Rig: sw sw trans
-- statement:
--   The Rig construction uses the sw sw trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L42-L44
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L42-L44

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

theorem SCCThm8.Rig.sw_sw_trans {A : Finset (Fin n)} {i j l : Fin n} (hj : j ∉ A) :
    sw (sw A i j) j l = sw A i l := by sorry
