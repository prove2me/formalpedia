-- Prove2me | Theorems.Thm_PI_WGL_EqvWt_weight_rowW_apply
-- name    : PI.WGL.EqvWt.weight_rowW_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:59:59.126316+00:00
-- url     : https://prove2.me/theorems/3ab185b4-ac21-58ff-b3ac-0fb3800271eb
-- title:
--   Eqv Wt: weight row W apply
-- statement:
--   The Eqv Wt construction uses the weight row W apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L63-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L63-L74

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

theorem PI.WGL.EqvWt.weight_rowW_apply {r c : ℕ} (m : Fin r × Fin c →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r c) m a = rowDeg m a := by sorry
