-- Prove2me | Theorems.Thm_SCCThm8_Rig_indep
-- name    : SCCThm8.Rig.indep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:49:39.591268+00:00
-- url     : https://prove2.me/theorems/f7e0e2e1-621d-4b4c-951e-8224ed79b11c
-- title:
--   Rig: indep
-- statement:
--   Step 2: independence of the swap ratio from the base set.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L102-L112
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/Rigidity.lean#L102-L112

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

theorem SCCThm8.Rig.indep (hk : 2 ≤ k)
    (hP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C → f₁ A * f₂ B * f₃ C = 1)
    {A A' : Finset (Fin (3 * k))} (hA : A.card = k) (hA' : A'.card = k) {i j : Fin (3 * k)}
    (hi : i ∈ A) (hi' : i ∈ A') (hj : j ∉ A) (hj' : j ∉ A') :
    f₁ (sw A i j) * (f₁ A)⁻¹ = f₁ (sw A' i j) * (f₁ A')⁻¹ := by sorry
