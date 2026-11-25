-- Prove2me | Theorems.Thm_SCCThm8_Rig_f3_swap
-- name    : SCCThm8.Rig.f3_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:49:30.811219+00:00
-- url     : https://prove2.me/theorems/2d61aa32-a6a8-4233-b239-2f3ffb3d2cee
-- title:
--   Rig: f3 swap
-- statement:
--   Swap rule for `f₃`.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L131-L142
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L131-L142

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

theorem SCCThm8.Rig.f3_swap (hk : 2 ≤ k)
    (hP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C → f₁ A * f₂ B * f₃ C = 1)
    (C : Finset (Fin (3 * k))) (hC : C.card = k) (j i : Fin (3 * k)) (hj : j ∈ C) (hi : i ∉ C) :
    f₃ (sw C j i) = f₃ C * (dl k f₁ i j)⁻¹ := by sorry
