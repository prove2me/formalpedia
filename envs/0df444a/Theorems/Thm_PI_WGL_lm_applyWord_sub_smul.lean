-- Prove2me | Theorems.Thm_PI_WGL_lm_applyWord_sub_smul
-- name    : PI.WGL.lm_applyWord_sub_smul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:46:19.352422+00:00
-- url     : https://prove2.me/theorems/523a39f6-eb6a-420b-808c-04eca47f3b69
-- title:
--   WGL: lm apply Word sub smul
-- statement:
--   The WGL construction uses the lm apply Word sub smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftAsm.lean#L67-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftAsm.lean#L67-L75

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftAsm
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

theorem PI.WGL.lm_applyWord_sub_smul {R : Type*} [CommRing R] {r m : ℕ} (w : List (Fin r × Fin r × ℕ)) (c : R)
    (f g : MvPolynomial (Fin r × Fin m) R) :
    applyWord R w (f - c • g) = applyWord R w f - c • applyWord R w g := by sorry
