-- Prove2me | Theorems.Thm_PI_WGL_io_last_emb
-- name    : PI.WGL.io_last_emb
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:46:26.764301+00:00
-- url     : https://prove2.me/theorems/04d4b2e9-ff3d-4246-93c9-2c9af22bedc9
-- title:
--   WGL: io last emb
-- statement:
--   The WGL construction uses the io last emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/IoExistsOfCap.lean#L175-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/IoExistsOfCap.lean#L175-L205

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

theorem PI.WGL.io_last_emb {n N : ℕ} (h : n + 1 = N) (a : ℂˣ) (g : GL (Fin n) ℂ) :
    lastGL ℂ N a * embGL ℂ n N h g = embGL ℂ n N h g * lastGL ℂ N a := by sorry
