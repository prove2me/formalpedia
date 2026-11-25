-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameMultiProjPrime_weight_mapDomain_51f3f05633c1
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameMultiProjPrime_weight_mapDomain_51f3f05633c1
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:36.61902+00:00
-- url     : https://prove2.me/theorems/c958e473-c435-4c7d-9f74-19c204aba99e
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Rename Multi Proj Prime weight map Domain 51f3f05633c1: P2 M Ground Theory Heights  Heights Field Numbers Rename Multi Proj Prime weight map Domain 51
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Rename Multi Proj Prime weight map Domain 51f3f05633c1 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Rename Multi Proj Prime weight map Domain 51f3f05633c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PRenameMultiProjPrime.lean#L18-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PRenameMultiProjPrime.lean#L18-L30

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameMultiProjPrime_weight_mapDomain_51f3f05633c1 (hσ : ∀ v, (σ v).1 = E v.1) (d : (Σ s, κ s) →₀ ℕ) :
    Finsupp.weight (blockWeight ι') (Finsupp.mapDomain σ d) =
      Finsupp.weight (blockWeight κ) d ∘ E.symm := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«RenameMultiProjPrime».«weight_mapDomain» := P2M_GroundTheory_Heights__Heights_FieldNumbers_RenameMultiProjPrime_weight_mapDomain_51f3f05633c1
