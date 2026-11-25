-- Prove2me | Theorems.Thm_PI_WGL_io_sqAct_mem
-- name    : PI.WGL.io_sqAct_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:46:47.09025+00:00
-- url     : https://prove2.me/theorems/3cadf1e4-e8e8-5693-894d-baa56d055280
-- title:
--   WGL: io sq Act mem
-- statement:
--   The WGL construction uses the io sq Act mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/IoExistsOfCap.lean#L144-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/IoExistsOfCap.lean#L144-L147

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

theorem PI.WGL.io_sqAct_mem {k : ℕ} (mu : DomWeight k) (g : GL (Fin k) ℂ) {f : MvPolynomial (Fin k × Fin k) ℂ}
    (hf : f ∈ nablaSq ℂ k mu) : sqAct ℂ k mu g f ∈ nablaSq ℂ k mu := by sorry
