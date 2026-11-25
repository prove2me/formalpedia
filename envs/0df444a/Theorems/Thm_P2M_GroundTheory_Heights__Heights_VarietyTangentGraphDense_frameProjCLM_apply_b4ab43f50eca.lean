-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_frameProjCLM_apply_b4ab43f50eca
-- name    : P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_frameProjCLM_apply_b4ab43f50eca
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:30:01.414426+00:00
-- url     : https://prove2.me/theorems/07ab8410-ee6a-5a75-9c6f-a5881571ca9c
-- title:
--   P2 M Ground Theory Heights  Heights Variety Tangent Graph Dense frame Proj CLM apply b4ab43f50eca: P2 M Ground Theory Heights  Heights Variety Tangent Graph Dense frame Proj CLM apply b4ab43f50eca
-- statement:
--   The P2 M Ground Theory Heights  Heights Variety Tangent Graph Dense frame Proj CLM apply b4ab43f50eca construction uses the P2 M Ground Theory Heights  Heights Variety Tangent Graph Dense frame Proj CLM apply b4ab43f50eca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarietyTangentGraphDense.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarietyTangentGraphDense.lean#L27-L30

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

theorem P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_frameProjCLM_apply_b4ab43f50eca {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (z : EuclideanSpace ℂ (Fin n)) : frameProjCLM b I z = frameProj b I z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VarietyTangentGraphDense».«frameProjCLM_apply» := P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_frameProjCLM_apply_b4ab43f50eca
