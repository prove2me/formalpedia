-- Prove2me | Theorems.Thm_PI_WGL_XiB_initMinor_ne
-- name    : PI.WGL.XiB.initMinor_ne
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:45:49.374823+00:00
-- url     : https://prove2.me/theorems/2ebe22f8-784d-414f-9bff-8cab8103703e
-- title:
--   Xi B: init Minor ne
-- statement:
--   The Xi B construction uses the init Minor ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/EvalInitMinorNormLe.lean#L281-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/EvalInitMinorNormLe.lean#L281-L307

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

theorem PI.WGL.XiB.initMinor_ne {N s : ℕ} (I : Fin s → Fin N) (hI : Function.Injective I) (hs : s ≤ N) :
    Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs ≠ 0 := by sorry
