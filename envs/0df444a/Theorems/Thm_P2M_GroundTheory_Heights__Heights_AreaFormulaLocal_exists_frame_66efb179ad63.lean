-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AreaFormulaLocal_exists_frame_66efb179ad63
-- name    : P2M_GroundTheory_Heights__Heights_AreaFormulaLocal_exists_frame_66efb179ad63
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:18:00.463876+00:00
-- url     : https://prove2.me/theorems/30580de7-1692-4960-a15b-8e79bcc1ec6b
-- title:
--   P2 M Ground Theory Heights  Heights Area Formula Local exists frame 66efb179ad63: P2 M Ground Theory Heights  Heights Area Formula Local exists frame 66efb179ad63
-- statement:
--   The P2 M Ground Theory Heights  Heights Area Formula Local exists frame 66efb179ad63 construction uses the P2 M Ground Theory Heights  Heights Area Formula Local exists frame 66efb179ad63 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PAreaFormulaLocal.lean#L30-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PAreaFormulaLocal.lean#L30-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsAreaFormulaLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphPiece
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAreaGraphPartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGraphJacContinuous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetImageAreaSetFrame
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaFormulaLocal
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
open MeasureTheory Module Set
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.AreaFormulaLocal

theorem P2M_GroundTheory_Heights__Heights_AreaFormulaLocal_exists_frame_66efb179ad63 {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (W : Submodule ℝ F) {k : ℕ} (hW : finrank ℝ W = k) :
    ∃ (m : ℕ) (c : F →L[ℝ] EuclideanSpace ℝ (Fin k)) (c' : F →L[ℝ] EuclideanSpace ℝ (Fin m)),
      (∀ z, ‖AreaGraphPiece.pairPt (c z) (c' z)‖ = ‖z‖) ∧ ∀ w ∈ W, c' w = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AreaFormulaLocal».«exists_frame» := P2M_GroundTheory_Heights__Heights_AreaFormulaLocal_exists_frame_66efb179ad63
