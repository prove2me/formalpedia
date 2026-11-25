-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_chartLin_eq_sum_8f8e04b94730
-- name    : P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_chartLin_eq_sum_8f8e04b94730
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:38.256002+00:00
-- url     : https://prove2.me/theorems/f4414961-8721-4fba-8d33-4e09c5758d25
-- title:
--   P2 M Ground Theory Heights  Heights Chart Norm Alg Closed chart Lin eq sum 8f8e04b94730: P2 M Ground Theory Heights  Heights Chart Norm Alg Closed chart Lin eq sum 8f8e04b94730
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Norm Alg Closed chart Lin eq sum 8f8e04b94730 construction uses the P2 M Ground Theory Heights  Heights Chart Norm Alg Closed chart Lin eq sum 8f8e04b94730 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartNormAlgClosed.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartNormAlgClosed.lean#L36-L42

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

theorem P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_chartLin_eq_sum_8f8e04b94730 (u : Fin n → F) :
    algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u) =
      ∑ m, algebraMap F (Localization.AtPrime p) (u m) •
        algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartNormAlgClosed».«chartLin_eq_sum» := P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_chartLin_eq_sum_8f8e04b94730
