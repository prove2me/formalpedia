-- Prove2me | Theorems.Thm_SCCThm8_Rig_sw_sw_comm
-- name    : SCCThm8.Rig.sw_sw_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:49:22.414179+00:00
-- url     : https://prove2.me/theorems/9b5a8135-00e1-4f9c-b822-c632ead06686
-- title:
--   Rig: sw sw comm
-- statement:
--   The Rig construction uses the sw sw comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L46-L48
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L46-L48

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

theorem SCCThm8.Rig.sw_sw_comm {A : Finset (Fin n)} {i i' j j' : Fin n} (h1 : i' ≠ j) (h2 : i' ≠ j') :
    sw (sw A i j) i' j' = sw (sw A i j') i' j := by sorry
