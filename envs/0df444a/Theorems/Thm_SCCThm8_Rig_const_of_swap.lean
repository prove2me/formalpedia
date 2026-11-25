-- Prove2me | Theorems.Thm_SCCThm8_Rig_const_of_swap
-- name    : SCCThm8.Rig.const_of_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:44.882403+00:00
-- url     : https://prove2.me/theorems/56ba1b30-733b-518f-a8e1-0870103bdd35
-- title:
--   Rig: const of swap
-- statement:
--   Connectivity: a function invariant under swaps is constant on `k`-sets.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L270-L296
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L270-L296

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

theorem SCCThm8.Rig.const_of_swap {X : Type*} {k : ℕ} (F : Finset (Fin n) → X)
    (h : ∀ A : Finset (Fin n), A.card = k → ∀ i j, i ∈ A → j ∉ A → F (sw A i j) = F A) :
    ∀ m, ∀ A A' : Finset (Fin n), A.card = k → A'.card = k → (A \ A').card = m → F A = F A' := by sorry
