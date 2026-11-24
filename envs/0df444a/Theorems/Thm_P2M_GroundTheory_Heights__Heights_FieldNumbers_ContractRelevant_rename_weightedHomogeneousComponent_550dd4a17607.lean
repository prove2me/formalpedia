-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_rename_weightedHomogeneousComponent_550dd4a17607
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_rename_weightedHomogeneousComponent_550dd4a17607
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:48.023169+00:00
-- url     : https://prove2.me/theorems/0ee28ea0-5215-4ca6-a712-937e884e916d
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Contract Relevant rename weighted Homogeneous Component 550dd4a17607: P2 M Ground Theory Heights  Heights Field Numbers Contract Relevant rename weigh
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Contract Relevant rename weighted Homogeneous Component 550dd4a17607 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Contract Relevant rename weighted Homogeneous Component 550dd4a17607 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/ContractRelevant.lean#L52-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/ContractRelevant.lean#L52-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractRelevant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers GroundTheory.Heights₂.Heights.FieldNumbers.ContractRelevant
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
variable {K K' : Type*} [DecidableEq K] [DecidableEq K'] {ι : K → Type*} {ι' : K' → Type*}
  {j : K → K'} {g : (Σ k, ι k) → (Σ k, ι' k)} (hgj : ∀ v, (g v).1 = j v.1)
include hgj

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_rename_weightedHomogeneousComponent_550dd4a17607 (hj : Function.Injective j)
    (hg : Function.Injective g) {R : Type*} [CommSemiring R] (b : K → ℕ)
    (f : MvPolynomial (Σ k, ι k) R) :
    rename g (weightedHomogeneousComponent (blockWeight ι) b f) =
      weightedHomogeneousComponent (blockWeight ι') (Function.extend j b 0) (rename g f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«ContractRelevant».«rename_weightedHomogeneousComponent» := P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_rename_weightedHomogeneousComponent_550dd4a17607
