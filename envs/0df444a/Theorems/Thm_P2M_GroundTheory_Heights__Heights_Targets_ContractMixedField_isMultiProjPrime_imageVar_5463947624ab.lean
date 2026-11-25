-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ContractMixedField_isMultiProjPrime_imageVar_5463947624ab
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ContractMixedField_isMultiProjPrime_imageVar_5463947624ab
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:44:13.733818+00:00
-- url     : https://prove2.me/theorems/3215b624-dce1-5d09-a7d2-c882f7f15b8d
-- title:
--   P2 M Ground Theory Heights  Heights Targets Contract Mixed Field is Multi Proj Prime image Var 5463947624ab: P2 M Ground Theory Heights  Heights Targets Contract Mixed Field is Multi Proj Prime image
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Contract Mixed Field is Multi Proj Prime image Var 5463947624ab construction uses the P2 M Ground Theory Heights  Heights Targets Contract Mixed Field is Multi Proj Prime image Var 5463947624ab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ContractMixedField.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ContractMixedField.lean#L36-L41

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
omit [Fintype K] [Fintype K']

theorem P2M_GroundTheory_Heights__Heights_Targets_ContractMixedField_isMultiProjPrime_imageVar_5463947624ab {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {W : Ideal (MRingOver F ι')} (hW : IsMultiProjPrime W) : IsMultiProjPrime (imageVar F v W) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ContractMixedField».«isMultiProjPrime_imageVar» := P2M_GroundTheory_Heights__Heights_Targets_ContractMixedField_isMultiProjPrime_imageVar_5463947624ab
