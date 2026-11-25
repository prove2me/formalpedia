-- Prove2me | Theorems.Thm_SCCThm8_PRig_blk
-- name    : SCCThm8.PRig.blk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:53:49.786859+00:00
-- url     : https://prove2.me/theorems/d7a3bc2a-d990-4dee-946e-ab65d709f8a2
-- title:
--   PRig: blk
-- statement:
--   The PRig construction uses the blk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerRigidity.lean#L180-L188
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerRigidity.lean#L180-L188

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

theorem SCCThm8.PRig.blk (hk : 2 ≤ k) (hP : Good k f₁ f₂ f₃) (A₀ : Fin m → Finset (Fin (3 * k)))
    (hA₀ : ∀ j, (A₀ j).card = k) (j : Fin m) :
    ∀ X : Finset (Fin (3 * k)), X.card = k → ∀ s t, s ∈ X → t ∉ X →
      f₁ (update A₀ j (sw X s t)) = D k f₁ j s t * f₁ (update A₀ j X) := by sorry
