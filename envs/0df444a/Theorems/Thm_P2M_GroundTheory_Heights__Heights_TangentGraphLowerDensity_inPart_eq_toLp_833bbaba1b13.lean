-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_inPart_eq_toLp_833bbaba1b13
-- name    : P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_inPart_eq_toLp_833bbaba1b13
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:40.721468+00:00
-- url     : https://prove2.me/theorems/85e22bf5-816f-440b-9d30-1825b4afd1f9
-- title:
--   P2 M Ground Theory Heights  Heights Tangent Graph Lower Density in Part eq to Lp 833bbaba1b13: P2 M Ground Theory Heights  Heights Tangent Graph Lower Density in Part eq to Lp 833bbaba1b13
-- statement:
--   The P2 M Ground Theory Heights  Heights Tangent Graph Lower Density in Part eq to Lp 833bbaba1b13 construction uses the P2 M Ground Theory Heights  Heights Tangent Graph Lower Density in Part eq to Lp 833bbaba1b13 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTangentGraphLowerDensity.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTangentGraphLowerDensity.lean#L35-L40

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

theorem P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_inPart_eq_toLp_833bbaba1b13 {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) :
    TangentGraphLowerDensity.inPart b I z = WithLp.toLp 2 (frameProj b I z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TangentGraphLowerDensity».«inPart_eq_toLp» := P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_inPart_eq_toLp_833bbaba1b13
