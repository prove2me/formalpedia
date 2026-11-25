-- Prove2me | Theorems.Thm_PI_WGL_lm_fockF_add
-- name    : PI.WGL.lm_fockF_add
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:58:49.844177+00:00
-- url     : https://prove2.me/theorems/bbabad55-08cb-569a-aced-88ed864192ad
-- title:
--   WGL: lm fock F add
-- statement:
--   The WGL construction uses the lm fock F add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftAsm.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftAsm.lean#L26-L34

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

theorem PI.WGL.lm_fockF_add {σ : Type*} (f1 f2 g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (f1 + f2) g = Formalism.REAL.fockF f1 g + Formalism.REAL.fockF f2 g := by sorry
