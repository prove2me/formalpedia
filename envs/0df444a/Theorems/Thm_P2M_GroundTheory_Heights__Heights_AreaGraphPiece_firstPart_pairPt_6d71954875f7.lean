-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_firstPart_pairPt_6d71954875f7
-- name    : P2M_GroundTheory_Heights__Heights_AreaGraphPiece_firstPart_pairPt_6d71954875f7
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:16:01.121133+00:00
-- url     : https://prove2.me/theorems/d20b9c6f-8a85-492e-9829-e2762299ac0c
-- title:
--   P2 M Ground Theory Heights  Heights Area Graph Piece first Part pair Pt 6d71954875f7: P2 M Ground Theory Heights  Heights Area Graph Piece first Part pair Pt 6d71954875f7
-- statement:
--   The P2 M Ground Theory Heights  Heights Area Graph Piece first Part pair Pt 6d71954875f7 construction uses the P2 M Ground Theory Heights  Heights Area Graph Piece first Part pair Pt 6d71954875f7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaGraphPiece.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaGraphPiece.lean#L28-L31

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

theorem P2M_GroundTheory_Heights__Heights_AreaGraphPiece_firstPart_pairPt_6d71954875f7 (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    firstPart (pairPt u w) = u := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AreaGraphPiece».«firstPart_pairPt» := P2M_GroundTheory_Heights__Heights_AreaGraphPiece_firstPart_pairPt_6d71954875f7
