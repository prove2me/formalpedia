-- Prove2me | Theorems.Thm_SCCThm8_Rig_mem_sw
-- name    : SCCThm8.Rig.mem_sw
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:24.16694+00:00
-- url     : https://prove2.me/theorems/9b29b0ad-3b4c-5f20-bc0b-2b94e35c9dbe
-- title:
--   Rig: mem sw
-- statement:
--   The Rig construction uses the mem sw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L18-L19
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L18-L19

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

theorem SCCThm8.Rig.mem_sw {A : Finset (Fin n)} {i j x : Fin n} : x ∈ sw A i j ↔ x = j ∨ (x ≠ i ∧ x ∈ A) := by sorry
