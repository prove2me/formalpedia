-- Prove2me | Theorems.Thm_PI_WGL_XiB_eval_initMinor_norm_le
-- name    : PI.WGL.XiB.eval_initMinor_norm_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:45:48.678219+00:00
-- url     : https://prove2.me/theorems/141f7159-4df0-4718-8291-526812502729
-- title:
--   Xi B: eval init Minor norm le
-- statement:
--   The Xi B construction uses the eval init Minor norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/EvalInitMinorNormLe.lean#L320-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/EvalInitMinorNormLe.lean#L320-L330

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

theorem PI.WGL.XiB.eval_initMinor_norm_le {N s : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (hx : x ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (I : Fin s → Fin N) (hI : Function.Injective I) (hs : s ≤ N) :
    ‖MvPolynomial.eval (fun v : Fin N × Fin N => x v.1 v.2) (Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs)‖ ≤ 1 := by sorry
