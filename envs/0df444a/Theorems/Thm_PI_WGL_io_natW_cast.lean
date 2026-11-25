-- Prove2me | Theorems.Thm_PI_WGL_io_natW_cast
-- name    : PI.WGL.io_natW_cast
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:04:10.040618+00:00
-- url     : https://prove2.me/theorems/75561668-9fea-4a97-a873-d01527ccc9bd
-- title:
--   WGL: io nat W cast
-- statement:
--   The WGL construction uses the io nat W cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/IoPolDiagHw.lean#L17-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/IoPolDiagHw.lean#L17-L30

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_CapelliShift
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoExistsOfCap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_BCRowGenMonomial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_IoPolDiagHw
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

theorem PI.WGL.io_natW_cast {k : ℕ} (mu : DomWeight k) (a : Fin k) :
    ((mu.natW a : ℕ) : ℂ) = ((mu.w a - mu.detShift : ℤ) : ℂ) := by sorry
