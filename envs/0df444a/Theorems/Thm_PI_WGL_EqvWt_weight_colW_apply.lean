-- Prove2me | Theorems.Thm_PI_WGL_EqvWt_weight_colW_apply
-- name    : PI.WGL.EqvWt.weight_colW_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:46:02.718323+00:00
-- url     : https://prove2.me/theorems/d9d93cc3-e782-407a-878a-b0ff8f0595b9
-- title:
--   Eqv Wt: weight col W apply
-- statement:
--   The Eqv Wt construction uses the weight col W apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L76-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L76-L85

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

theorem PI.WGL.EqvWt.weight_colW_apply {r c : ℕ} (m : Fin r × Fin c →₀ ℕ) (j : Fin c) :
    Finsupp.weight (colW r c) m j = ∑ a, m (a, j) := by sorry
