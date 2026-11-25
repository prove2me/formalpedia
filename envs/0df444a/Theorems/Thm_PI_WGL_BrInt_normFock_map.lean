-- Prove2me | Theorems.Thm_PI_WGL_BrInt_normFock_map
-- name    : PI.WGL.BrInt.normFock_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:59:32.793627+00:00
-- url     : https://prove2.me/theorems/75c04a37-0550-5fac-bb2f-b53d6503f32e
-- title:
--   Br Int: norm Fock map
-- statement:
--   The Br Int construction uses the norm Fock map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/ConstructionBrInt.lean#L175-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/ConstructionBrInt.lean#L175-L179

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ConstructionBrInt
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

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

theorem PI.WGL.BrInt.normFock_map {N : ℕ} (lam : DomWeight N) (a b : MvPolynomial (Fin N × Fin N) ℚ) :
    normFock lam (map (algebraMap ℚ ℂ) a) (map (algebraMap ℚ ℂ) b) = ((normFockQ lam a b : ℚ) : ℂ) := by sorry
