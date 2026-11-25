-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_exists_near_off_c08368d72ca2
-- name    : P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_exists_near_off_c08368d72ca2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:43:21.945371+00:00
-- url     : https://prove2.me/theorems/78a0f72e-85b3-4d6c-8344-65ca27736cb6
-- title:
--   P2 M Ground Theory Heights  Heights Variety Tangent Graph Dense exists near off c08368d72ca2: P2 M Ground Theory Heights  Heights Variety Tangent Graph Dense exists near off c08368d72ca2
-- statement:
--   The P2 M Ground Theory Heights  Heights Variety Tangent Graph Dense exists near off c08368d72ca2 construction uses the P2 M Ground Theory Heights  Heights Variety Tangent Graph Dense exists near off c08368d72ca2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarietyTangentGraphDense.lean#L40-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarietyTangentGraphDense.lean#L40-L68

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyTangentGraphDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZeroSetOpenMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFramePlaneGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFramePlaneGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameGraphGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameJacobianGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PJacobianRankGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PConormalGenerationGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameImplicitGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNullSmaller
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarietyTangentGraphDense
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
open MvPolynomial Topology Filter MeasureTheory
noncomputable section
open GroundTheory.Heights₂.Heights.VarietyTangentGraphDense

theorem P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_exists_near_off_c08368d72ca2 {n d : ℕ} {J J' : Ideal (MvPolynomial (Fin n) ℂ)}
    (hO : IndefiniteRowSideFullHecke.ComplexSets.ZeroSetOpenMass.Statement) (hJ : J.IsPrime)
    (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d)
    (hJ' : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J') < d) {z : EuclideanSpace ℂ (Fin n)}
    (hz : z ∈ zeroSetEuc J) {ε : ℝ} (hε : 0 < ε) :
    ∃ z₁ ∈ zeroSetEuc J \ zeroSetEuc J', dist z₁ z < ε := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VarietyTangentGraphDense».«exists_near_off» := P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_exists_near_off_c08368d72ca2
