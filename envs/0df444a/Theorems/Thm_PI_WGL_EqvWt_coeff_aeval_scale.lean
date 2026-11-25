-- Prove2me | Theorems.Thm_PI_WGL_EqvWt_coeff_aeval_scale
-- name    : PI.WGL.EqvWt.coeff_aeval_scale
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:46:52.8758+00:00
-- url     : https://prove2.me/theorems/843bcbef-417b-4d81-aca1-34ef1458096e
-- title:
--   Eqv Wt: coeff aeval scale
-- statement:
--   The Eqv Wt construction uses the coeff aeval scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L11-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L11-L25

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

theorem PI.WGL.EqvWt.coeff_aeval_scale {σ : Type} (e : σ → ℂ) (f : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    coeff m (aeval (fun v => C (e v) * X v) f) = (m.prod fun v k => e v ^ k) * coeff m f := by sorry
