-- Prove2me | Theorems.Thm_SCCThm8_Rig_ex2
-- name    : SCCThm8.Rig.ex2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:49:39.141447+00:00
-- url     : https://prove2.me/theorems/a6ea8472-0c57-4ca7-9e50-25f186ac0eb4
-- title:
--   Rig: ex2
-- statement:
--   The Rig construction uses the ex2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L159-L163
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L159-L163

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

theorem SCCThm8.Rig.ex2 (hk : 2 ≤ k) {i j l : Fin (3 * k)} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    ∃ A : Finset (Fin (3 * k)), A.card = k ∧ i ∈ A ∧ j ∉ A ∧ l ∉ A := by sorry
