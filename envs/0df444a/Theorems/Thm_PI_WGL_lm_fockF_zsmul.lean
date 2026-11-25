-- Prove2me | Theorems.Thm_PI_WGL_lm_fockF_zsmul
-- name    : PI.WGL.lm_fockF_zsmul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:02:26.755974+00:00
-- url     : https://prove2.me/theorems/e20f83c6-29bf-4538-913c-5ebaa1c3a8f9
-- title:
--   WGL: lm fock F zsmul
-- statement:
--   The WGL construction uses the lm fock F zsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftAsm.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftAsm.lean#L44-L46

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

theorem PI.WGL.lm_fockF_zsmul {σ : Type*} (a : ℤ) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (a • f) g = a * Formalism.REAL.fockF f g := by sorry
