-- Prove2me | Theorems.Thm_SCCThm8_PRig_D_spec
-- name    : SCCThm8.PRig.D_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:48:57.468778+00:00
-- url     : https://prove2.me/theorems/428c3956-dc49-50d4-a06c-fe3e52c1675e
-- title:
--   PRig: D spec
-- statement:
--   The PRig construction uses the D spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerRigidity.lean#L150-L158
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerRigidity.lean#L150-L158

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

theorem SCCThm8.PRig.D_spec (hk : 2 ≤ k) (hP : Good k f₁ f₂ f₃) (A : Fin m → Finset (Fin (3 * k)))
    (hA : ∀ j, (A j).card = k) (j : Fin m) (s t : Fin (3 * k)) (hs : s ∈ A j) (ht : t ∉ A j) :
    f₁ (update A j (sw (A j) s t)) = D k f₁ j s t * f₁ A := by sorry
