-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ContractMixedField_intNum_eq_zero_51f6673158ff
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ContractMixedField_intNum_eq_zero_51f6673158ff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:44:01.369971+00:00
-- url     : https://prove2.me/theorems/eeba0e03-d5d4-56a6-8695-5412dbd0b8dd
-- title:
--   P2 M Ground Theory Heights  Heights Targets Contract Mixed Field int Num eq zero 51f6673158ff: P2 M Ground Theory Heights  Heights Targets Contract Mixed Field int Num eq zero 51f6673158ff
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Contract Mixed Field int Num eq zero 51f6673158ff construction uses the P2 M Ground Theory Heights  Heights Targets Contract Mixed Field int Num eq zero 51f6673158ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ContractMixedField.lean#L89-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ContractMixedField.lean#L89-L152

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsFieldIntersectionExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyBridgeFull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ContractMixedField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.Targets.ContractMixedField
variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
open Classical

theorem P2M_GroundTheory_Heights__Heights_Targets_ContractMixedField_intNum_eq_zero_51f6673158ff [DecidableEq K'] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v) :
    ∀ (n : ℕ) (V' : Ideal (MRingOver F ι')) (d₀ : ℕ) (bs : Fin n → K' → ℤ),
      IsProjVarF V' n → IsProjVarF (imageVar F v V') d₀ →
      d₀ < (∑ i, if ∃ a : K → ℤ, bs i = pullDeg κ a then 1 else 0) →
      NumbersDVR.intNum F V' bs = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ContractMixedField».«intNum_eq_zero» := P2M_GroundTheory_Heights__Heights_Targets_ContractMixedField_intNum_eq_zero_51f6673158ff
