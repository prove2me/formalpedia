-- Prove2me | Theorems.Thm_PI_WGL_io_fixed_up
-- name    : PI.WGL.io_fixed_up
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:47:11.510049+00:00
-- url     : https://prove2.me/theorems/f314187c-0a2d-4ecb-8c80-65dd45faf248
-- title:
--   WGL: io fixed up
-- statement:
--   The WGL construction uses the io fixed up property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/IoXiHw.lean#L9-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/IoXiHw.lean#L9-L51

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

theorem PI.WGL.io_fixed_up {n : ℕ} (lam : DomWeight (n + 1)) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hU : ∀ g : GL (Fin n) ℂ, (∀ i j, j < i → g i j = 0) → (∀ i, g i i = 1) →
      sqAct ℂ (n + 1) lam (embGL ℂ n (n + 1) rfl g) f = f)
    (a b : Fin n) (hab : a < b) : pol ℂ a.castSucc b.castSucc f = 0 := by sorry
