-- Prove2me | Theorems.Thm_SCCThm8_PRig_ctx
-- name    : SCCThm8.PRig.ctx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:53:01.225365+00:00
-- url     : https://prove2.me/theorems/43f23003-b251-5545-96ea-43bdafcd8150
-- title:
--   PRig: ctx
-- statement:
--   The PRig construction uses the ctx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerRigidity.lean#L87-L106
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerRigidity.lean#L87-L106

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

theorem SCCThm8.PRig.ctx (hP : Good k f₁ f₂ f₃) {A B C : Fin m → Finset (Fin (3 * k))}
    (hA : ∀ j, (A j).card = k) (hB : ∀ j, (B j).card = k) (hC : ∀ j, (C j).card = k)
    (hD : ∀ j, Disjoint (A j) (B j) ∧ Disjoint (A j) (C j) ∧ Disjoint (B j) (C j)) (j : Fin m) :
    ∀ X Y Z : Finset (Fin (3 * k)), X.card = k → Y.card = k → Z.card = k →
      Disjoint X Y → Disjoint X Z → Disjoint Y Z →
      f₁ (update A j X) * f₂ (update B j Y) * f₃ (update C j Z) = 1 := by sorry
