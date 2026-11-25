-- Prove2me | Theorems.Thm_SCCThm8_Rig_ex4
-- name    : SCCThm8.Rig.ex4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:49:53.898031+00:00
-- url     : https://prove2.me/theorems/8682299e-62c5-45ef-abd5-54b75e1764ce
-- title:
--   Rig: ex4
-- statement:
--   The Rig construction uses the ex4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L165-L171
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L165-L171

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

theorem SCCThm8.Rig.ex4 (hk : 2 ≤ k) {i i' j j' : Fin (3 * k)} (h1 : i ≠ i') (h2 : i ≠ j) (h3 : i ≠ j')
    (h4 : i' ≠ j) (h5 : i' ≠ j') (h6 : j ≠ j') :
    ∃ A : Finset (Fin (3 * k)), A.card = k ∧ i ∈ A ∧ i' ∈ A ∧ j ∉ A ∧ j' ∉ A := by sorry
