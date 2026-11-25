-- Prove2me | Theorems.Thm_PI_WGL_io_sqAct_smul
-- name    : PI.WGL.io_sqAct_smul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:51:32.034735+00:00
-- url     : https://prove2.me/theorems/d463dff6-b28f-50d9-8b86-7c431b3ef1e1
-- title:
--   WGL: io sq Act smul
-- statement:
--   The WGL construction uses the io sq Act smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/IoExistsOfCap.lean#L135-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/IoExistsOfCap.lean#L135-L138

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

theorem PI.WGL.io_sqAct_smul {k : ℕ} (mu : DomWeight k) (g : GL (Fin k) ℂ) (c : ℂ)
    (x : MvPolynomial (Fin k × Fin k) ℂ) : sqAct ℂ k mu g (c • x) = c • sqAct ℂ k mu g x := by sorry
