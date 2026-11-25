-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_realGraphPt_injective_e476b3e7ecac
-- name    : P2M_GroundTheory_Heights__Heights_realGraphPt_injective_e476b3e7ecac
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:50:08.07419+00:00
-- url     : https://prove2.me/theorems/6ac16dc6-da01-43fe-b3f5-9bf4fcda0d69
-- title:
--   P2 M Ground Theory Heights  Heights real Graph Pt injective e476b3e7ecac: P2 M Ground Theory Heights  Heights real Graph Pt injective e476b3e7ecac
-- statement:
--   The P2 M Ground Theory Heights  Heights real Graph Pt injective e476b3e7ecac construction uses the P2 M Ground Theory Heights  Heights real Graph Pt injective e476b3e7ecac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaGraphBound.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAreaGraphBound.lean#L14-L18

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

theorem P2M_GroundTheory_Heights__Heights_realGraphPt_injective_e476b3e7ecac {k m : ℕ} (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)) :
    Function.Injective (realGraphPt F) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«realGraphPt_injective» := P2M_GroundTheory_Heights__Heights_realGraphPt_injective_e476b3e7ecac
