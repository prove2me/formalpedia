-- Prove2me | Theorems.Thm_PI_WGL_io_sqAct_mul
-- name    : PI.WGL.io_sqAct_mul
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:52:20.303327+00:00
-- url     : https://prove2.me/theorems/6de1f20c-b829-5759-ac70-42c4b657da19
-- title:
--   WGL: io sq Act mul
-- statement:
--   The WGL construction uses the io sq Act mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/IoExistsOfCap.lean#L149-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/IoExistsOfCap.lean#L149-L166

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
import Definitions.Def_Formalism_PeriodIntegrals_GTBranch
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoExistsOfCap
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
open Formalism.BasicNotions MvPolynomial

theorem PI.WGL.io_sqAct_mul {k : ℕ} (mu : DomWeight k) (g g' : GL (Fin k) ℂ) (f : MvPolynomial (Fin k × Fin k) ℂ) :
    sqAct ℂ k mu (g * g') f = sqAct ℂ k mu g (sqAct ℂ k mu g' f) := by sorry
