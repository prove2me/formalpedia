-- Prove2me | Theorems.Thm_SCCThm8_PRig_indepP
-- name    : SCCThm8.PRig.indepP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:53:00.06146+00:00
-- url     : https://prove2.me/theorems/9443347f-4b21-5d1d-a0aa-f8b6ed261afb
-- title:
--   PRig: indep P
-- statement:
--   Independence of the swap ratio from the whole tuple.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerRigidity.lean#L126-L142
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerRigidity.lean#L126-L142

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
variable {G : Type*} [Group G] {k m : ℕ} {f₁ f₂ f₃ : (Fin m → Finset (Fin (3 * k))) → G}

theorem SCCThm8.PRig.indepP (hk : 2 ≤ k) (hP : Good k f₁ f₂ f₃) {A A' : Fin m → Finset (Fin (3 * k))}
    (hA : ∀ j, (A j).card = k) (hA' : ∀ j, (A' j).card = k) {j : Fin m} {s t : Fin (3 * k)}
    (hs : s ∈ A j) (hs' : s ∈ A' j) (ht : t ∉ A j) (ht' : t ∉ A' j) :
    f₁ (update A j (sw (A j) s t)) * (f₁ A)⁻¹ = f₁ (update A' j (sw (A' j) s t)) * (f₁ A')⁻¹ := by sorry
