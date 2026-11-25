-- Prove2me | Theorems.Thm_SCCThm8_PRig_coreP
-- name    : SCCThm8.PRig.coreP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:53:32.079012+00:00
-- url     : https://prove2.me/theorems/04c9b0d7-964e-5136-9f46-fb415c39f9a0
-- title:
--   PRig: core P
-- statement:
--   Core of the argument, in a commutative group mapping to `G`.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerRigidity.lean#L230-L283
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerRigidity.lean#L230-L283

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

theorem SCCThm8.PRig.coreP {G : Type*} [Group G] {k m : ℕ} {f₁ f₂ f₃ : (Fin m → Finset (Fin (3 * k))) → G}
    (hP : Good k f₁ f₂ f₃)
    {H : Type*} [CommGroup H] (φ : H →* G) (g' : Fin m → Fin (3 * k) → H)
    (hs1 : ∀ A : Fin m → Finset (Fin (3 * k)), (∀ j, (A j).card = k) → ∀ j s t, s ∈ A j →
      t ∉ A j → f₁ (update A j (sw (A j) s t)) = φ (g' j t * (g' j s)⁻¹) * f₁ A)
    (hs3 : ∀ C : Fin m → Finset (Fin (3 * k)), (∀ j, (C j).card = k) → ∀ j t s, t ∈ C j →
      s ∉ C j → f₃ (update C j (sw (C j) t s)) = f₃ C * φ (g' j s * (g' j t)⁻¹))
    (A B C : Fin m → Finset (Fin (3 * k))) (hA : ∀ j, (A j).card = k)
    (hB : ∀ j, (B j).card = k) (hC : ∀ j, (C j).card = k) :
    f₁ A * f₂ B * f₃ C = φ (∏ j, ∏ i, g' j i ^ (multP A B C j i - 1)) := by sorry
