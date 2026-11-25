-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularityValuationCentre_ker_isMultiHomogIdeal_9d702971f25a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RegularityValuationCentre_ker_isMultiHomogIdeal_9d702971f25a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:14.956318+00:00
-- url     : https://prove2.me/theorems/3454e195-7986-4bb9-a59f-651e3d96006f
-- title:
--   P2 M Ground Theory Heights  Heights Inter Regularity Valuation Centre ker is Multi Homog Ideal 9d702971f25a: P2 M Ground Theory Heights  Heights Inter Regularity Valuation Centre ker is Multi Homog Id
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Regularity Valuation Centre ker is Multi Homog Ideal 9d702971f25a construction uses the P2 M Ground Theory Heights  Heights Inter Regularity Valuation Centre ker is Multi Homog Ideal 9d702971f25a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/KerIsMultiHomogIdeal.lean#L62-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/KerIsMultiHomogIdeal.lean#L62-L69

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
set_option backward.isDefEq.respectTransparency.types false

theorem P2M_GroundTheory_Heights__Heights_Inter_RegularityValuationCentre_ker_isMultiHomogIdeal_9d702971f25a [DecidableEq K] {E : Type*} [Field E] (ψ : MRing ι →+* E) :
    IsMultiHomogIdeal (RingHom.ker (RegularityFunctionFieldNumber.specMap ψ ∅)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RegularityValuationCentre».«ker_isMultiHomogIdeal» := P2M_GroundTheory_Heights__Heights_Inter_RegularityValuationCentre_ker_isMultiHomogIdeal_9d702971f25a
