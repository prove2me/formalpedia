-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ContractMixedField_isMultiHomog_rename_70c5fc34d2e4
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ContractMixedField_isMultiHomog_rename_70c5fc34d2e4
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:23:34.004721+00:00
-- url     : https://prove2.me/theorems/bdd0ffe1-d9cb-47f3-b9a4-8918fb5f2488
-- title:
--   P2 M Ground Theory Heights  Heights Targets Contract Mixed Field is Multi Homog rename 70c5fc34d2e4: P2 M Ground Theory Heights  Heights Targets Contract Mixed Field is Multi Homog rename 70c5fc34d2e4
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Contract Mixed Field is Multi Homog rename 70c5fc34d2e4 construction uses the P2 M Ground Theory Heights  Heights Targets Contract Mixed Field is Multi Homog rename 70c5fc34d2e4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ContractMixedField.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ContractMixedField.lean#L23-L32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsFieldIntersectionExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyBridgeFull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ContractMixedField
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_rename_fd9a6cb3fd55

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

theorem P2M_GroundTheory_Heights__Heights_Targets_ContractMixedField_isMultiHomog_rename_70c5fc34d2e4 {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} (hv : IsBlockMap κ v)
    {t : MRingOver F ι} {a : K → ℕ} (ht : IsMultiHomog t a) :
    IsMultiHomog (rename v t) (Function.extend κ a 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ContractMixedField».«isMultiHomog_rename» := P2M_GroundTheory_Heights__Heights_Targets_ContractMixedField_isMultiHomog_rename_70c5fc34d2e4
