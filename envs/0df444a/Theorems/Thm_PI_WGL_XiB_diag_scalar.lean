-- Prove2me | Theorems.Thm_PI_WGL_XiB_diag_scalar
-- name    : PI.WGL.XiB.diag_scalar
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:46:56.017793+00:00
-- url     : https://prove2.me/theorems/e1df7c12-e657-4ba2-9e54-dae80edefb40
-- title:
--   Xi B: diag scalar
-- statement:
--   The Xi B construction uses the diag scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/EvalInitMinorNormLe.lean#L30-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/EvalInitMinorNormLe.lean#L30-L106

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

theorem PI.WGL.XiB.diag_scalar {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    (s : Fin N → ℂˣ) :
    detPow ℂ N (diagGL ℂ N s) lam.detShift * XiA.xiScal h lam sg (Matrix.diagonal fun a => (s a : ℂ)) =
      (((∏ j : Fin n, s ⟨j.1, by omega⟩ ^ sg.w j) * s ⟨n, by omega⟩ ^ degZ lam sg : ℂˣ) : ℂ) := by sorry
