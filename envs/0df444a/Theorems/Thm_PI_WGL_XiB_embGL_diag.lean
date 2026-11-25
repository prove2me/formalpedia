-- Prove2me | Theorems.Thm_PI_WGL_XiB_embGL_diag
-- name    : PI.WGL.XiB.embGL_diag
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:59:00.323157+00:00
-- url     : https://prove2.me/theorems/8da3ba30-090d-5443-b2e2-c3edcba2dd05
-- title:
--   Xi B: emb GL diag
-- statement:
--   The Xi B construction uses the emb GL diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/EvalInitMinorNormLe.lean#L128-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/EvalInitMinorNormLe.lean#L128-L150

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

theorem PI.WGL.XiB.embGL_diag {n N : ℕ} (h : n + 1 = N) (t : Fin n → ℂˣ) :
    embGL ℂ n N h (diagGL ℂ n t) = diagGL ℂ N (fun a => if ha : a.1 < n then t ⟨a.1, ha⟩ else 1) := by sorry
