-- Prove2me | Theorems.Thm_PI_WGL_XiB_xi_unitri
-- name    : PI.WGL.XiB.xi_unitri
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:46:21.338861+00:00
-- url     : https://prove2.me/theorems/881fde07-323e-4ec4-acf9-6acc228b86ba
-- title:
--   Xi B: xi unitri
-- statement:
--   The Xi B construction uses the xi unitri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/EvalInitMinorNormLe.lean#L171-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/EvalInitMinorNormLe.lean#L171-L214

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

theorem PI.WGL.XiB.xi_unitri {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (g : GL (Fin n) ℂ) (hlow : ∀ i j, j < i → (g : Matrix (Fin n) (Fin n) ℂ) i j = 0)
    (hdiag : ∀ i, (g : Matrix (Fin n) (Fin n) ℂ) i i = 1) :
    sqAct ℂ N lam (embGL ℂ n N h g) (xi ℂ h lam sg) = xi ℂ h lam sg := by sorry
