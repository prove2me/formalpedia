-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaGraphPiece_norm_le_norm_pairPt_b076ae4cab32
-- name    : P2M_GroundTheory_Heights__Heights_AreaGraphPiece_norm_le_norm_pairPt_b076ae4cab32
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:15:45.055193+00:00
-- url     : https://prove2.me/theorems/a0f4c730-f20d-4764-97dc-3e1dd67f4217
-- title:
--   P2 M Ground Theory Heights  Heights Area Graph Piece norm le norm pair Pt b076ae4cab32: P2 M Ground Theory Heights  Heights Area Graph Piece norm le norm pair Pt b076ae4cab32
-- statement:
--   The P2 M Ground Theory Heights  Heights Area Graph Piece norm le norm pair Pt b076ae4cab32 construction uses the P2 M Ground Theory Heights  Heights Area Graph Piece norm le norm pair Pt b076ae4cab32 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaGraphPiece.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaGraphPiece.lean#L57-L60

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

theorem P2M_GroundTheory_Heights__Heights_AreaGraphPiece_norm_le_norm_pairPt_b076ae4cab32 (u : EuclideanSpace ℝ (Fin k)) (w : EuclideanSpace ℝ (Fin m)) :
    ‖u‖ ≤ ‖pairPt u w‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AreaGraphPiece».«norm_le_norm_pairPt» := P2M_GroundTheory_Heights__Heights_AreaGraphPiece_norm_le_norm_pairPt_b076ae4cab32
