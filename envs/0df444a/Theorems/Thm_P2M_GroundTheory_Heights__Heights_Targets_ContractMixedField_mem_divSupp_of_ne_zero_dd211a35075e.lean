-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ContractMixedField_mem_divSupp_of_ne_zero_dd211a35075e
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ContractMixedField_mem_divSupp_of_ne_zero_dd211a35075e
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:41:11.568903+00:00
-- url     : https://prove2.me/theorems/ccc64380-6c2c-4cab-8d03-cb871c75fad5
-- title:
--   P2 M Ground Theory Heights  Heights Targets Contract Mixed Field mem div Supp of ne zero dd211a35075e: P2 M Ground Theory Heights  Heights Targets Contract Mixed Field mem div Supp of ne zero dd211a35
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Contract Mixed Field mem div Supp of ne zero dd211a35075e construction uses the P2 M Ground Theory Heights  Heights Targets Contract Mixed Field mem div Supp of ne zero dd211a35075e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ContractMixedField.lean#L51-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ContractMixedField.lean#L51-L56

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ContractMixedField_mem_divSupp_of_ne_zero_dd211a35075e {P : Ideal (MRingOver F ι)} {s : MRingOver F ι} {W : Ideal (MRingOver F ι)}
    (h : divCycle P s W ≠ 0) : W ∈ divSupp P s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ContractMixedField».«mem_divSupp_of_ne_zero» := P2M_GroundTheory_Heights__Heights_Targets_ContractMixedField_mem_divSupp_of_ne_zero_dd211a35075e
