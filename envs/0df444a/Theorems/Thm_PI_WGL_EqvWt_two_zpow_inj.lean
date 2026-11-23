-- Prove2me | Theorems.Thm_PI_WGL_EqvWt_two_zpow_inj
-- name    : PI.WGL.EqvWt.two_zpow_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:57:56.985196+00:00
-- url     : https://prove2.me/theorems/2e2e23e6-e62a-4943-ac00-9cbb6df88bba
-- title:
--   Eqv Wt: two zpow inj
-- statement:
--   The Eqv Wt construction uses the two zpow inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L126-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftEqvWt.lean#L126-L130

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

theorem PI.WGL.EqvWt.two_zpow_inj {k l : ℤ} (e : (2 : ℂ) ^ k = (2 : ℂ) ^ l) : k = l := by sorry
