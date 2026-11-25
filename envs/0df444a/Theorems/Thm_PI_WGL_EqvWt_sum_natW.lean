-- Prove2me | Theorems.Thm_PI_WGL_EqvWt_sum_natW
-- name    : PI.WGL.EqvWt.sum_natW
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:48:17.531848+00:00
-- url     : https://prove2.me/theorems/a762878a-74a1-4609-a62c-de5f9cdd6b2d
-- title:
--   Eqv Wt: sum nat W
-- statement:
--   The Eqv Wt construction uses the sum nat W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L111-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L111-L124

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

theorem PI.WGL.EqvWt.sum_natW {r : ℕ} (lam : DomWeight r) :
    ((∑ j, lam.natW j : ℕ) : ℤ) = wsum lam - r * lam.detShift := by sorry
