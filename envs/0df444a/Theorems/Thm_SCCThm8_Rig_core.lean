-- Prove2me | Theorems.Thm_SCCThm8_Rig_core
-- name    : SCCThm8.Rig.core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:51:13.750807+00:00
-- url     : https://prove2.me/theorems/476fe402-1528-55be-9913-189402021a18
-- title:
--   Rig: core
-- statement:
--   Core of the argument, in a commutative group mapping to `G`.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L321-L366
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L321-L366

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

theorem SCCThm8.Rig.core {G : Type*} [Group G] {k : ℕ} {f₁ f₂ f₃ : Finset (Fin (3 * k)) → G}
    (hP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C → f₁ A * f₂ B * f₃ C = 1)
    {H : Type*} [CommGroup H] (φ : H →* G) (g' : Fin (3 * k) → H)
    (hs1 : ∀ A : Finset (Fin (3 * k)), A.card = k → ∀ i j, i ∈ A → j ∉ A →
      f₁ (sw A i j) = φ (g' j * (g' i)⁻¹) * f₁ A)
    (hs3 : ∀ C : Finset (Fin (3 * k)), C.card = k → ∀ j i, j ∈ C → i ∉ C →
      f₃ (sw C j i) = f₃ C * φ (g' i * (g' j)⁻¹))
    (A B C : Finset (Fin (3 * k))) (hA : A.card = k) (hB : B.card = k) (hC : C.card = k) :
    f₁ A * f₂ B * f₃ C = φ (∏ i, g' i ^ (mult A B C i - 1)) := by sorry
