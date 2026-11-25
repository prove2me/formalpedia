-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_norm_sq_split_85435cb7ec5f
-- name    : P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_norm_sq_split_85435cb7ec5f
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:39.548362+00:00
-- url     : https://prove2.me/theorems/bea738f3-4f7a-464d-86e8-5830d2f58f88
-- title:
--   P2 M Ground Theory Heights  Heights Tangent Graph Lower Density norm sq split 85435cb7ec5f: P2 M Ground Theory Heights  Heights Tangent Graph Lower Density norm sq split 85435cb7ec5f
-- statement:
--   The P2 M Ground Theory Heights  Heights Tangent Graph Lower Density norm sq split 85435cb7ec5f construction uses the P2 M Ground Theory Heights  Heights Tangent Graph Lower Density norm sq split 85435cb7ec5f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTangentGraphLowerDensity.lean#L42-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTangentGraphLowerDensity.lean#L42-L51

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

theorem P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_norm_sq_split_85435cb7ec5f {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) :
    ‖z‖ ^ 2 = ‖TangentGraphLowerDensity.inPart b I z‖ ^ 2 + ‖TangentGraphLowerDensity.outPart b I z‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TangentGraphLowerDensity».«norm_sq_split» := P2M_GroundTheory_Heights__Heights_TangentGraphLowerDensity_norm_sq_split_85435cb7ec5f
