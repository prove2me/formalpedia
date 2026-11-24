-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_isMultiProjPrime_comap_rename_bb5f689a2f30
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_isMultiProjPrime_comap_rename_bb5f689a2f30
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:50.533584+00:00
-- url     : https://prove2.me/theorems/89eb5de7-4dbd-45ce-aca2-0d52a1ef043c
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Contract Relevant is Multi Proj Prime comap rename bb5f689a2f30: P2 M Ground Theory Heights  Heights Field Numbers Contract Relevant is Multi Proj Pri
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Contract Relevant is Multi Proj Prime comap rename bb5f689a2f30 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Contract Relevant is Multi Proj Prime comap rename bb5f689a2f30 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/ContractRelevant.lean#L72-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/ContractRelevant.lean#L72-L88

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_isMultiProjPrime_comap_rename_bb5f689a2f30 (hj : Function.Injective j) (hg : Function.Injective g)
    (hsurj : ∀ w : Σ k, ι' k, w.1 ∈ Set.range j → ∃ v, g v = w) {R : Type*} [CommRing R]
    {P : Ideal (MRing ι' R)} (hP : IsMultiProjPrime P) :
    IsMultiProjPrime (P.comap (rename (R := R) g)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«ContractRelevant».«isMultiProjPrime_comap_rename» := P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_isMultiProjPrime_comap_rename_bb5f689a2f30
