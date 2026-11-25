-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ContractMixedField_exists_dim_107ce925eca8
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ContractMixedField_exists_dim_107ce925eca8
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:14.8369+00:00
-- url     : https://prove2.me/theorems/f3df3fed-cbf6-4ffd-9714-478749f66d7b
-- title:
--   P2 M Ground Theory Heights  Heights Targets Contract Mixed Field exists dim 107ce925eca8: P2 M Ground Theory Heights  Heights Targets Contract Mixed Field exists dim 107ce925eca8
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Contract Mixed Field exists dim 107ce925eca8 construction uses the P2 M Ground Theory Heights  Heights Targets Contract Mixed Field exists dim 107ce925eca8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ContractMixedField.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ContractMixedField.lean#L43-L49

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ContractMixedField_exists_dim_107ce925eca8 {V : Ideal (MRingOver F ι)} (hV : IsMultiProjPrime V) :
    ∃ D : ℕ, Fintype.card K ≤ D ∧ ringKrullDim (MRingOver F ι ⧸ V) = D := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ContractMixedField».«exists_dim» := P2M_GroundTheory_Heights__Heights_Targets_ContractMixedField_exists_dim_107ce925eca8
