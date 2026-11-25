-- Prove2me | Theorems.Thm_PI_WGL_XiB_xi_mem
-- name    : PI.WGL.XiB.xi_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:59:44.006804+00:00
-- url     : https://prove2.me/theorems/c8bc9204-55bb-5095-9f03-10c1b98074dd
-- title:
--   Xi B: xi mem
-- statement:
--   The Xi B construction uses the xi mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/EvalInitMinorNormLe.lean#L263-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/EvalInitMinorNormLe.lean#L263-L279

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

theorem PI.WGL.XiB.xi_mem {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg) :
    xi ℂ h lam sg ∈ nablaSq ℂ N lam := by sorry
