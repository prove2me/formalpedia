-- Prove2me | Theorems.Thm_PI_WGL_LTB_card_eq_val
-- name    : PI.WGL.LTB.card_eq_val
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:47:41.581351+00:00
-- url     : https://prove2.me/theorems/ba1661c4-7e08-4e80-842d-ac54bbeb6276
-- title:
--   LTB: card eq val
-- statement:
--   The LTB construction uses the card eq val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L166-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L166-L175

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

theorem PI.WGL.LTB.card_eq_val {m n : ℕ} (a : Fin n) :
    (Finset.univ.filter fun p : Fin m => p.1 = a.1).card = if a.1 < m then 1 else 0 := by sorry
