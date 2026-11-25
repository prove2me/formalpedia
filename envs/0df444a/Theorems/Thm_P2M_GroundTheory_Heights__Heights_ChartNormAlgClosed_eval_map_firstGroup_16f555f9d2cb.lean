-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_eval_map_firstGroup_16f555f9d2cb
-- name    : P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_eval_map_firstGroup_16f555f9d2cb
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:15:40.198806+00:00
-- url     : https://prove2.me/theorems/7b981fa0-7cc6-54a8-80fb-a3b429976ed5
-- title:
--   P2 M Ground Theory Heights  Heights Chart Norm Alg Closed eval map first Group 16f555f9d2cb: P2 M Ground Theory Heights  Heights Chart Norm Alg Closed eval map first Group 16f555f9d2cb
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Norm Alg Closed eval map first Group 16f555f9d2cb construction uses the P2 M Ground Theory Heights  Heights Chart Norm Alg Closed eval map first Group 16f555f9d2cb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartNormAlgClosed.lean#L111-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PChartNormAlgClosed.lean#L111-L129

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

theorem P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_eval_map_firstGroup_16f555f9d2cb {F : Type} [Field F] {n e : ℕ} (p : Ideal (MvPolynomial (Fin e × Fin n) F))
    [p.IsPrime] (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F) :
    eval (fun m => algebraMap F (Localization.AtPrime p) (u m))
        (map (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) (firstGroup f)) =
      algebraMap _ (Localization.AtPrime p) (specFirst f u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartNormAlgClosed».«eval_map_firstGroup» := P2M_GroundTheory_Heights__Heights_ChartNormAlgClosed_eval_map_firstGroup_16f555f9d2cb
