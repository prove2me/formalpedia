-- Prove2me | Theorems.Thm_PI_WGL_EqvWt_coeff_sqAct_diag
-- name    : PI.WGL.EqvWt.coeff_sqAct_diag
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:02:16.139859+00:00
-- url     : https://prove2.me/theorems/d463bd2e-94f6-4a2a-91d8-4d5af96cb300
-- title:
--   Eqv Wt: coeff sq Act diag
-- statement:
--   The Eqv Wt construction uses the coeff sq Act diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L46-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L46-L61

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

theorem PI.WGL.EqvWt.coeff_sqAct_diag {r : ℕ} (lam : DomWeight r) (t : Fin r → ℂˣ) (f : MvPolynomial (Fin r × Fin r) ℂ)
    (m : Fin r × Fin r →₀ ℕ) :
    coeff m (sqAct ℂ r lam (diagGL ℂ r t) f) =
      (∏ a, (t a : ℂ)) ^ lam.detShift * ((∏ a, (t a : ℂ) ^ rowDeg m a) * coeff m f) := by sorry
