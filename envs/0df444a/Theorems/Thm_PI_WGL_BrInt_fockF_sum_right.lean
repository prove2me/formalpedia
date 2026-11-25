-- Prove2me | Theorems.Thm_PI_WGL_BrInt_fockF_sum_right
-- name    : PI.WGL.BrInt.fockF_sum_right
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:47:58.622126+00:00
-- url     : https://prove2.me/theorems/edfcc3b7-b8ea-4ca6-b9b6-445a5307127d
-- title:
--   Br Int: fock F sum right
-- statement:
--   The Br Int construction uses the fock F sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/ConstructionBrInt.lean#L38-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/ConstructionBrInt.lean#L38-L45

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ConstructionBrInt
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
open PI.WGL.BrInt
open Formalism.REAL Formalism.GradedWeylDivisibility
variable {σ : Type}

theorem PI.WGL.BrInt.fockF_sum_right {ι : Type*} (s : Finset ι) (f : MvPolynomial σ ℂ) (c : ι → ℂ)
    (g : ι → MvPolynomial σ ℂ) :
    fockF f (∑ i ∈ s, c i • g i) = ∑ i ∈ s, star (c i) * fockF f (g i) := by sorry
