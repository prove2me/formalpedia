-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_adjoin_eq_top_f8fef9005cd6
-- name    : P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_adjoin_eq_top_f8fef9005cd6
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:16:12.508003+00:00
-- url     : https://prove2.me/theorems/327b55d5-c6e2-547b-9403-278d56a5562e
-- title:
--   P2 M Ground Theory Heights  Heights Chart Norm Alg Closed adjoin eq top f8fef9005cd6: P2 M Ground Theory Heights  Heights Chart Norm Alg Closed adjoin eq top f8fef9005cd6
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Norm Alg Closed adjoin eq top f8fef9005cd6 construction uses the P2 M Ground Theory Heights  Heights Chart Norm Alg Closed adjoin eq top f8fef9005cd6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartNormAlgClosed.lean#L51-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartNormAlgClosed.lean#L51-L107

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

theorem P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_adjoin_eq_top_f8fef9005cd6 :
    Algebra.adjoin (Localization.AtPrime p)
        (Set.range fun m => algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m))) = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartNormAlgClosed».«adjoin_eq_top» := P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_adjoin_eq_top_f8fef9005cd6
