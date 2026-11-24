-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_algebraMap_tower_bc962cfa3117
-- name    : P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_algebraMap_tower_bc962cfa3117
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:58.987892+00:00
-- url     : https://prove2.me/theorems/19652f36-6441-42c2-b1de-f5c57507f9ed
-- title:
--   P2 M Ground Theory Heights  Heights Chart Norm Alg Closed algebra Map tower bc962cfa3117: P2 M Ground Theory Heights  Heights Chart Norm Alg Closed algebra Map tower bc962cfa3117
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Norm Alg Closed algebra Map tower bc962cfa3117 construction uses the P2 M Ground Theory Heights  Heights Chart Norm Alg Closed algebra Map tower bc962cfa3117 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartNormAlgClosed.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartNormAlgClosed.lean#L20-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroupDvd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartNormAlgClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartNormSep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChartNormAlgClosed
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartNormAlgClosed
variable {F : Type} [Field F] {n e : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)
  (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_algebraMap_tower_bc962cfa3117 (x : MvPolynomial (Fin e × Fin n) F) :
    algebraMap (Localization.AtPrime p) (ChartLoc I t e p) (algebraMap _ _ x) =
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (algebraMap _ (ChartInc I t e) x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartNormAlgClosed».«algebraMap_tower» := P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_algebraMap_tower_bc962cfa3117
