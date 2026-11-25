-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_pairPt_sub_f54c10fbd1af
-- name    : P2M_GroundTheory_Heights__Heights_AreaGraphPiece_pairPt_sub_f54c10fbd1af
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:16:27.877152+00:00
-- url     : https://prove2.me/theorems/57894f72-ae20-4bd5-a827-9c0429f766c2
-- title:
--   P2 M Ground Theory Heights  Heights Area Graph Piece pair Pt sub f54c10fbd1af: P2 M Ground Theory Heights  Heights Area Graph Piece pair Pt sub f54c10fbd1af
-- statement:
--   The P2 M Ground Theory Heights  Heights Area Graph Piece pair Pt sub f54c10fbd1af construction uses the P2 M Ground Theory Heights  Heights Area Graph Piece pair Pt sub f54c10fbd1af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaGraphPiece.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaGraphPiece.lean#L38-L41

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

theorem P2M_GroundTheory_Heights__Heights_AreaGraphPiece_pairPt_sub_f54c10fbd1af (u u' : EuclideanSpace ℝ (Fin k)) (w w' : EuclideanSpace ℝ (Fin m)) :
    pairPt u w - pairPt u' w' = pairPt (u - u') (w - w') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AreaGraphPiece».«pairPt_sub» := P2M_GroundTheory_Heights__Heights_AreaGraphPiece_pairPt_sub_f54c10fbd1af
