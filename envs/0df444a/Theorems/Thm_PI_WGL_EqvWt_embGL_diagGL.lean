-- Prove2me | Theorems.Thm_PI_WGL_EqvWt_embGL_diagGL
-- name    : PI.WGL.EqvWt.embGL_diagGL
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:45:51.130881+00:00
-- url     : https://prove2.me/theorems/8f3bf089-9c49-474d-8b80-3b7e205b4a7e
-- title:
--   Eqv Wt: emb GL diag GL
-- statement:
--   The Eqv Wt construction uses the emb GL diag GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L132-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L132-L139

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftEqvWt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
open PI.WGL.EqvWt

theorem PI.WGL.EqvWt.embGL_diagGL {n : ℕ} (t : Fin n → ℂˣ) :
    embGL ℂ n (n + 1) rfl (diagGL ℂ n t) =
      diagGL ℂ (n + 1) (fun a => if ha : a.1 < n then t ⟨a.1, ha⟩ else 1) := by sorry
