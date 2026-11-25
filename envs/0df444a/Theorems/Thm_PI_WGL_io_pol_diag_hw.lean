-- Prove2me | Theorems.Thm_PI_WGL_io_pol_diag_hw
-- name    : PI.WGL.io_pol_diag_hw
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:54:24.164808+00:00
-- url     : https://prove2.me/theorems/3caf80c4-209f-5e1b-9cbf-3862f7e4f327
-- title:
--   WGL: io pol diag hw
-- statement:
--   The WGL construction uses the io pol diag hw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/IoPolDiagHw.lean#L32-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/IoPolDiagHw.lean#L32-L55

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

theorem PI.WGL.io_pol_diag_hw {k : ℕ} (ν : Fin k → ℕ) (hν : Antitone ν) (a : Fin k) :
    pol ℂ a a (hw ℂ (le_refl k) ν) = ((ν a : ℕ) : ℂ) • hw ℂ (le_refl k) ν := by sorry
