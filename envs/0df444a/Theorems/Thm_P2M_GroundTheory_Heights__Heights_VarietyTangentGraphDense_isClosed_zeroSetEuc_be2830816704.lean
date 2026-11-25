-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_isClosed_zeroSetEuc_be2830816704
-- name    : P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_isClosed_zeroSetEuc_be2830816704
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:42:31.128639+00:00
-- url     : https://prove2.me/theorems/33217078-edcc-406b-9814-65ec5f033818
-- title:
--   P2 M Ground Theory Heights  Heights Variety Tangent Graph Dense is Closed zero Set Euc be2830816704: P2 M Ground Theory Heights  Heights Variety Tangent Graph Dense is Closed zero Set Euc be2830816704
-- statement:
--   The P2 M Ground Theory Heights  Heights Variety Tangent Graph Dense is Closed zero Set Euc be2830816704 construction uses the P2 M Ground Theory Heights  Heights Variety Tangent Graph Dense is Closed zero Set Euc be2830816704 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarietyTangentGraphDense.lean#L32-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarietyTangentGraphDense.lean#L32-L38

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

theorem P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_isClosed_zeroSetEuc_be2830816704 {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSetEuc J) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VarietyTangentGraphDense».«isClosed_zeroSetEuc» := P2M_GroundTheory_Heights__Heights_VarietyTangentGraphDense_isClosed_zeroSetEuc_be2830816704
