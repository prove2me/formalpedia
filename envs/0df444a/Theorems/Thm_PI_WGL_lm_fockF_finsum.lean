-- Prove2me | Theorems.Thm_PI_WGL_lm_fockF_finsum
-- name    : PI.WGL.lm_fockF_finsum
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:49:55.876918+00:00
-- url     : https://prove2.me/theorems/4337c55f-9d45-526a-894d-eb6322b75599
-- title:
--   WGL: lm fock F finsum
-- statement:
--   The WGL construction uses the lm fock F finsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftAsm.lean#L48-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftAsm.lean#L48-L55

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

theorem PI.WGL.lm_fockF_finsum {σ ι : Type*} (s : Finset ι) (y : ι → MvPolynomial σ ℂ) (g : MvPolynomial σ ℂ)
    (h0 : ∀ i ∈ s, Formalism.REAL.fockF (y i) g = 0) : Formalism.REAL.fockF (∑ i ∈ s, y i) g = 0 := by sorry
