-- Prove2me | Theorems.Thm_SCCThm8_PRig_D_cross
-- name    : SCCThm8.PRig.D_cross
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:53:40.117463+00:00
-- url     : https://prove2.me/theorems/22a4de93-58ac-4a77-b11a-86f58d9b0799
-- title:
--   PRig: D cross
-- statement:
--   The PRig construction uses the D cross property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerRigidity.lean#L190-L225
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/SCCThm8/PowerRigidity.lean#L190-L225

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

theorem SCCThm8.PRig.D_cross (hk : 2 ≤ k) (hP : Good k f₁ f₂ f₃) {j j' : Fin m} (hjj : j ≠ j')
    {s t s' t' : Fin (3 * k)} (hst : s ≠ t) (hst' : s' ≠ t') :
    D k f₁ j s t * D k f₁ j' s' t' = D k f₁ j' s' t' * D k f₁ j s t := by sorry
