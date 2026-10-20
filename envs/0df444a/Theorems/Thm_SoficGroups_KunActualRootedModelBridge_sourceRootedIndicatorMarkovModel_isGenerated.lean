-- Prove2me | Theorems.Thm_SoficGroups_KunActualRootedModelBridge_sourceRootedIndicatorMarkovModel_isGenerated
-- name    : SoficGroups.KunActualRootedModelBridge.sourceRootedIndicatorMarkovModel_isGenerated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/49945a61-8146-4482-b973-787ff2a435d5
-- title:
--   SoficGroups.KunActualRootedModelBridge.sourceRootedIndicatorMarkovModel_isGenerated
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualRootedModelBridge
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunRootedWordPower
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators
universe u

theorem SoficGroups.KunActualRootedModelBridge.sourceRootedIndicatorMarkovModel_isGenerated
    {G : Type} [Group G] [DecidableEq G]
    (A : SoficGroups.SoficApproximation G)
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤)
    (n : ℕ) (T : Finset (Fin (A.model n).size)) :
    (sourceRootedIndicatorMarkovModel
      A S hsymmetric hgenerates n T).IsGenerated
        (fun i : ↥S => (i : G))
        (symmetricGeneratorWord S hsymmetric hgenerates) := by sorry
