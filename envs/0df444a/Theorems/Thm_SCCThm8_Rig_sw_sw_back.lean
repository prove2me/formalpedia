-- Prove2me | Theorems.Thm_SCCThm8_Rig_sw_sw_back
-- name    : SCCThm8.Rig.sw_sw_back
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:27.16109+00:00
-- url     : https://prove2.me/theorems/e2a9e010-d4d1-5f78-9261-f8d7edf01c28
-- title:
--   Rig: sw sw back
-- statement:
--   The Rig construction uses the sw sw back property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L38-L40
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L38-L40

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

theorem SCCThm8.Rig.sw_sw_back {A : Finset (Fin n)} {i j : Fin n} (hi : i ∈ A) (hj : j ∉ A) :
    sw (sw A i j) j i = A := by sorry
