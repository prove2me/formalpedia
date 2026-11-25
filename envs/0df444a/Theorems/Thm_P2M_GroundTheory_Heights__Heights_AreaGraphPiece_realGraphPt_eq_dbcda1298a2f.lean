-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_realGraphPt_eq_dbcda1298a2f
-- name    : P2M_GroundTheory_Heights__Heights_AreaGraphPiece_realGraphPt_eq_dbcda1298a2f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:15:11.383004+00:00
-- url     : https://prove2.me/theorems/b53fd3a7-7917-4cd6-9c09-e06321a6b8f2
-- title:
--   P2 M Ground Theory Heights  Heights Area Graph Piece real Graph Pt eq dbcda1298a2f: P2 M Ground Theory Heights  Heights Area Graph Piece real Graph Pt eq dbcda1298a2f
-- statement:
--   The P2 M Ground Theory Heights  Heights Area Graph Piece real Graph Pt eq dbcda1298a2f construction uses the P2 M Ground Theory Heights  Heights Area Graph Piece real Graph Pt eq dbcda1298a2f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaGraphPiece.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaGraphPiece.lean#L25-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAreaGraphPiece
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_VolumeLtHausdorffUnitBallTwenty
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphPiece
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
open MeasureTheory Module
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
open GroundTheory.Heights₂.Heights.AreaGraphPiece
variable {k m : ℕ}

theorem P2M_GroundTheory_Heights__Heights_AreaGraphPiece_realGraphPt_eq_dbcda1298a2f (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin k)) : realGraphPt F x = pairPt x (F x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AreaGraphPiece».«realGraphPt_eq» := P2M_GroundTheory_Heights__Heights_AreaGraphPiece_realGraphPt_eq_dbcda1298a2f
