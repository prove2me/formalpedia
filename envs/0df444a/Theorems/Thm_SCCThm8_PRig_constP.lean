-- Prove2me | Theorems.Thm_SCCThm8_PRig_constP
-- name    : SCCThm8.PRig.constP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:52:56.790685+00:00
-- url     : https://prove2.me/theorems/8ad8da18-0033-4bcc-8235-b72d0ba74a36
-- title:
--   PRig: const P
-- statement:
--   Connectivity for tuples: a function invariant under blockwise swaps is constant on tuples
--   of `k`-sets.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerRigidity.lean#L18-L59
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerRigidity.lean#L18-L59

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_PowerRigidity
set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.PRig
open Rig Function

theorem SCCThm8.PRig.constP {n m k : ℕ} {X : Type*} (F : (Fin m → Finset (Fin n)) → X)
    (h : ∀ A : Fin m → Finset (Fin n), (∀ j, (A j).card = k) → ∀ j s t, s ∈ A j → t ∉ A j →
      F (update A j (sw (A j) s t)) = F A)
    (A A' : Fin m → Finset (Fin n)) (hA : ∀ j, (A j).card = k) (hA' : ∀ j, (A' j).card = k) :
    F A = F A' := by sorry
