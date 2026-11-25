-- Prove2me | Theorems.Thm_PI_WGL_EqvWt_prod_rowDeg
-- name    : PI.WGL.EqvWt.prod_rowDeg
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:46:52.935422+00:00
-- url     : https://prove2.me/theorems/96dce42c-90cf-4eaa-8b0a-cce0ed41bb26
-- title:
--   Eqv Wt: prod row Deg
-- statement:
--   The Eqv Wt construction uses the prod row Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L38-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L38-L44

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftEqvWt
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod

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

theorem PI.WGL.EqvWt.prod_rowDeg {r c : ℕ} (x : Fin r → ℂ) (m : Fin r × Fin c →₀ ℕ) :
    (m.prod fun v k => x v.1 ^ k) = ∏ a, x a ^ rowDeg m a := by sorry
