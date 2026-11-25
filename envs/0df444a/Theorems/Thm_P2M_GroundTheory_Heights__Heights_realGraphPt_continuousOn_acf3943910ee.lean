-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_realGraphPt_continuousOn_acf3943910ee
-- name    : P2M_GroundTheory_Heights__Heights_realGraphPt_continuousOn_acf3943910ee
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:49:58.52533+00:00
-- url     : https://prove2.me/theorems/c08f19db-cccb-423c-98ca-fb1351d4b213
-- title:
--   P2 M Ground Theory Heights  Heights real Graph Pt continuous On acf3943910ee: P2 M Ground Theory Heights  Heights real Graph Pt continuous On acf3943910ee
-- statement:
--   The P2 M Ground Theory Heights  Heights real Graph Pt continuous On acf3943910ee construction uses the P2 M Ground Theory Heights  Heights real Graph Pt continuous On acf3943910ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaGraphBound.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaGraphBound.lean#L20-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaGraphBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaGraphPiece
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaGraphPartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGraphJacContinuous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphBound
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
open MeasureTheory
open scoped ENNReal NNReal

theorem P2M_GroundTheory_Heights__Heights_realGraphPt_continuousOn_acf3943910ee {k m : ℕ} {F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)}
    {s : Set (EuclideanSpace ℝ (Fin k))} (hF : ContinuousOn F s) : ContinuousOn (realGraphPt F) s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«realGraphPt_continuousOn» := P2M_GroundTheory_Heights__Heights_realGraphPt_continuousOn_acf3943910ee
