-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_inPart_apply_572a6cb21cc2
-- name    : P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_inPart_apply_572a6cb21cc2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:15.63149+00:00
-- url     : https://prove2.me/theorems/c1137283-5b8a-4496-8ac8-fe65b2bd13da
-- title:
--   P2 M Ground Theory Heights  Heights Tangent Graph Lower Density in Part apply 572a6cb21cc2: P2 M Ground Theory Heights  Heights Tangent Graph Lower Density in Part apply 572a6cb21cc2
-- statement:
--   The P2 M Ground Theory Heights  Heights Tangent Graph Lower Density in Part apply 572a6cb21cc2 construction uses the P2 M Ground Theory Heights  Heights Tangent Graph Lower Density in Part apply 572a6cb21cc2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTangentGraphLowerDensity.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTangentGraphLowerDensity.lean#L23-L27

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTangentGraphLowerDensity
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyLelongMono
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTangentGraphLowerDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_inPart_apply_572a6cb21cc2 {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (i : I) :
    TangentGraphLowerDensity.inPart b I z i = inner ℂ (b i) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TangentGraphLowerDensity».«inPart_apply» := P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_inPart_apply_572a6cb21cc2
