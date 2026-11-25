-- Prove2me | Theorems.Thm_SCCThm8_PRig_f3_swapP
-- name    : SCCThm8.PRig.f3_swapP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:53:48.185799+00:00
-- url     : https://prove2.me/theorems/766bbcd1-9afd-4766-94f1-aa6c972f54db
-- title:
--   PRig: f3 swap P
-- statement:
--   The PRig construction uses the f3 swap P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerRigidity.lean#L160-L178
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerRigidity.lean#L160-L178

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

theorem SCCThm8.PRig.f3_swapP (hk : 2 ≤ k) (hP : Good k f₁ f₂ f₃) (C : Fin m → Finset (Fin (3 * k)))
    (hC : ∀ j, (C j).card = k) (j : Fin m) (t s : Fin (3 * k)) (ht : t ∈ C j) (hs : s ∉ C j) :
    f₃ (update C j (sw (C j) t s)) = f₃ C * (D k f₁ j s t)⁻¹ := by sorry
