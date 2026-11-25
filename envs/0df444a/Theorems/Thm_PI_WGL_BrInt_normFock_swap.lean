-- Prove2me | Theorems.Thm_PI_WGL_BrInt_normFock_swap
-- name    : PI.WGL.BrInt.normFock_swap
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:46:29.627432+00:00
-- url     : https://prove2.me/theorems/0a85e89e-a1e4-4164-bc46-081dd38139fa
-- title:
--   Br Int: norm Fock swap
-- statement:
--   The Br Int construction uses the norm Fock swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/ConstructionBrInt.lean#L218-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/ConstructionBrInt.lean#L218-L221

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

theorem PI.WGL.BrInt.normFock_swap {N : ℕ} (lam : DomWeight N) (f g : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam g f = star (normFock lam f g) := by sorry
