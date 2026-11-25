-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityValuationCentre_specMap_component_5a8b2558d033
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularityValuationCentre_specMap_component_5a8b2558d033
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:25:43.6968+00:00
-- url     : https://prove2.me/theorems/c597902a-2183-413a-8222-20692ea47e2b
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularity Valuation Centre spec Map component 5a8b2558d033: P2 M Ground Theory Heights  Heights Inter Regularity Valuation Centre spec Map component 5a8b2558
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularity Valuation Centre spec Map component 5a8b2558d033 construction uses the P2 M Ground Theory Heights  Heights Inter Regularity Valuation Centre spec Map component 5a8b2558d033 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/KerIsMultiHomogIdeal.lean#L34-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/KerIsMultiHomogIdeal.lean#L34-L58

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsIntValuationLtOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_KerIsMultiHomogIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open GroundTheory.Heights₂.Heights.Inter.RegularityValuationCentre
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularityValuationCentre_specMap_component_5a8b2558d033 [DecidableEq K] {E : Type*} [Field E] (ψ : MRing ι →+* E) (k : K) (d : ℕ)
    (g : MRing ι) :
    RegularityFunctionFieldNumber.specMap ψ ∅ (weightedHomogeneousComponent (blockWeight k) d g) =
      weightedHomogeneousComponent (tWeight k) d (RegularityFunctionFieldNumber.specMap ψ ∅ g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularityValuationCentre».«specMap_component» := P2M_GroundTheory_Heights__Heights_Inter_RegularityValuationCentre_specMap_component_5a8b2558d033
