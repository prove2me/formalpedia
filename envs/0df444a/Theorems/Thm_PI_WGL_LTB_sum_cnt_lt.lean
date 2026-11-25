-- Prove2me | Theorems.Thm_PI_WGL_LTB_sum_cnt_lt
-- name    : PI.WGL.LTB.sum_cnt_lt
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:44:14.54779+00:00
-- url     : https://prove2.me/theorems/1e656d18-d4ef-4bc4-a86b-a6ce69d096b5
-- title:
--   LTB: sum cnt lt
-- statement:
--   The LTB construction uses the sum cnt lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L80-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L80-L96

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTM

theorem PI.WGL.LTB.sum_cnt_lt {n K : ℕ} {sz : Fin K → ℕ} (J : ∀ k, Fin (sz k) → Fin n) (t : ℕ) :
    ∑ k, (Finset.univ.filter fun p : Fin (sz k) => (J k p).1 < t).card =
      ∑ a ∈ Finset.univ.filter (fun a : Fin n => a.1 < t), tupCnt J a := by sorry
