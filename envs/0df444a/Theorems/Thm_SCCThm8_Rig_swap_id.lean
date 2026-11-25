-- Prove2me | Theorems.Thm_SCCThm8_Rig_swap_id
-- name    : SCCThm8.Rig.swap_id
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:09.845558+00:00
-- url     : https://prove2.me/theorems/253906ed-c7e8-4444-9785-40f54bcaffe0
-- title:
--   Rig: swap id
-- statement:
--   Step 1: the swap identity.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L58-L99
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L58-L99

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
variable {G : Type*} [Group G] {k : ℕ} {f₁ f₂ f₃ : Finset (Fin (3 * k)) → G}

theorem SCCThm8.Rig.swap_id
    (hP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C → f₁ A * f₂ B * f₃ C = 1)
    {A C : Finset (Fin (3 * k))} (hA : A.card = k) (hC : C.card = k) (hAC : Disjoint A C)
    {i j : Fin (3 * k)} (hi : i ∈ A) (hj : j ∈ C) :
    f₁ (sw A i j) * (f₁ A)⁻¹ = (f₃ (sw C j i))⁻¹ * f₃ C := by sorry
