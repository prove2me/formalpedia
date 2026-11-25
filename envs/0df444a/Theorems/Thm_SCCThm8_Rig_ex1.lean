-- Prove2me | Theorems.Thm_SCCThm8_Rig_ex1
-- name    : SCCThm8.Rig.ex1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:50.382654+00:00
-- url     : https://prove2.me/theorems/fc6203d0-bde3-4f47-bc94-c89bc2ff82a5
-- title:
--   Rig: ex1
-- statement:
--   The Rig construction uses the ex1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L153-L157
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L153-L157

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
variable {G : Type*} [Group G] {k : ℕ} {F : Finset (Fin (3 * k)) → G}
  {d : Fin (3 * k) → Fin (3 * k) → G}

theorem SCCThm8.Rig.ex1 (hk : 2 ≤ k) {i j : Fin (3 * k)} (hij : i ≠ j) :
    ∃ A : Finset (Fin (3 * k)), A.card = k ∧ i ∈ A ∧ j ∉ A := by sorry
