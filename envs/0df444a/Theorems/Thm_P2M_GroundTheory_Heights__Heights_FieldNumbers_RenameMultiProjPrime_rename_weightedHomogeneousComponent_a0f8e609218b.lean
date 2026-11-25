-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameMultiProjPrime_rename_weightedHomogeneousComponent_a0f8e609218b
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameMultiProjPrime_rename_weightedHomogeneousComponent_a0f8e609218b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:37.675384+00:00
-- url     : https://prove2.me/theorems/5368b251-8e85-4b75-a4f3-18d7297e76d4
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Rename Multi Proj Prime rename weighted Homogeneous Component a0f8e609218b: P2 M Ground Theory Heights  Heights Field Numbers Rename Multi Proj Prime
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Rename Multi Proj Prime rename weighted Homogeneous Component a0f8e609218b construction uses the P2 M Ground Theory Heights  Heights Field Numbers Rename Multi Proj Prime rename weighted Homogeneous Component a0f8e609218b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PRenameMultiProjPrime.lean#L32-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PRenameMultiProjPrime.lean#L32-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsRename
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiProjPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.RenameMultiProjPrime
variable {S K' : Type} [DecidableEq S] [DecidableEq K'] {κ : S → Type} {ι' : K' → Type} (E : S ≃ K')
  (σ : (Σ s, κ s) ≃ (Σ k', ι' k'))

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameMultiProjPrime_rename_weightedHomogeneousComponent_a0f8e609218b {R : Type u} [CommRing R]
    (hσ : ∀ v, (σ v).1 = E v.1) (b : S → ℕ) (f : MRing κ R) :
    rename σ (weightedHomogeneousComponent (blockWeight κ) b f) =
      weightedHomogeneousComponent (blockWeight ι') (b ∘ E.symm) (rename σ f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«RenameMultiProjPrime».«rename_weightedHomogeneousComponent» := P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameMultiProjPrime_rename_weightedHomogeneousComponent_a0f8e609218b
