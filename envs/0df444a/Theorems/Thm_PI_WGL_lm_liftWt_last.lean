-- Prove2me | Theorems.Thm_PI_WGL_lm_liftWt_last
-- name    : PI.WGL.lm_liftWt_last
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:46:36.526333+00:00
-- url     : https://prove2.me/theorems/a2b5c2e4-69e7-46a3-9b1c-1aebb9f8c672
-- title:
--   WGL: lm lift Wt last
-- statement:
--   The WGL construction uses the lm lift Wt last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftAsm.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftAsm.lean#L97-L100

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

theorem PI.WGL.lm_liftWt_last {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n) (ω : Fin n → ℕ) :
    liftWt h lam mu ω ⟨N - 1, by omega⟩ = dLast lam mu := by sorry
