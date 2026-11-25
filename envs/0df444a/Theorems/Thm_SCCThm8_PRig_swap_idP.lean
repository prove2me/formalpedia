-- Prove2me | Theorems.Thm_SCCThm8_PRig_swap_idP
-- name    : SCCThm8.PRig.swap_idP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:49:03.208642+00:00
-- url     : https://prove2.me/theorems/23a05c95-0a3a-557b-a9b6-8b253f322838
-- title:
--   PRig: swap id P
-- statement:
--   Swap identity for tuples.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerRigidity.lean#L109-L123
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerRigidity.lean#L109-L123

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

theorem SCCThm8.PRig.swap_idP (hP : Good k f₁ f₂ f₃) {A C : Fin m → Finset (Fin (3 * k))}
    (hA : ∀ j, (A j).card = k) (hC : ∀ j, (C j).card = k) (hAC : ∀ j, Disjoint (A j) (C j))
    {j : Fin m} {s t : Fin (3 * k)} (hs : s ∈ A j) (ht : t ∈ C j) :
    f₁ (update A j (sw (A j) s t)) * (f₁ A)⁻¹ = (f₃ (update C j (sw (C j) t s)))⁻¹ * f₃ C := by sorry
