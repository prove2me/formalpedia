-- Prove2me | Theorems.Thm_PI_WGL_io_torus_diag
-- name    : PI.WGL.io_torus_diag
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:52:03.412346+00:00
-- url     : https://prove2.me/theorems/69b50471-5661-573b-9a12-09a0f3e7f3ea
-- title:
--   WGL: io torus diag
-- statement:
--   The WGL construction uses the io torus diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/IoXiHw.lean#L53-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/IoXiHw.lean#L53-L98

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoPolDiagHw
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoXiHw
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

theorem PI.WGL.io_torus_diag {n : ℕ} (lam : DomWeight (n + 1)) (sg : DomWeight n)
    (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hT : ∀ t : Fin n → ℂˣ, sqAct ℂ (n + 1) lam (embGL ℂ n (n + 1) rfl (diagGL ℂ n t)) f =
      ((∏ j, t j ^ sg.w j : ℂˣ) : ℂ) • f)
    (a : Fin n) (hd : lam.detShift ≤ sg.w a) :
    pol ℂ a.castSucc a.castSucc f = ((sg.w a - lam.detShift : ℤ) : ℂ) • f := by sorry
