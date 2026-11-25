-- Prove2me | Theorems.Thm_PI_WGL_XiB_xi_unitary
-- name    : PI.WGL.XiB.xi_unitary
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:46:18.366467+00:00
-- url     : https://prove2.me/theorems/edb0a553-337b-414d-9599-03adac5d91b2
-- title:
--   Xi B: xi unitary
-- statement:
--   The Xi B construction uses the xi unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/EvalInitMinorNormLe.lean#L332-L344
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/EvalInitMinorNormLe.lean#L332-L344

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_RowsZStrictMono
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_EvalInitMinorNormLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.XiB
open Formalism.BasicNotions MvPolynomial

theorem PI.WGL.XiB.xi_unitary {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (x : Matrix (Fin N) (Fin N) ℂ) (hx : x ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    ‖MvPolynomial.eval (fun v : Fin N × Fin N => x v.1 v.2) (xi ℂ h lam sg)‖ ≤ 1 := by sorry
