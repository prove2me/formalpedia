-- Prove2me | Theorems.Thm_PI_WGL_lm_liftWt_inj
-- name    : PI.WGL.lm_liftWt_inj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:03:11.210602+00:00
-- url     : https://prove2.me/theorems/e0ef6423-26fe-57a1-ae3a-cf91d5e797e8
-- title:
--   WGL: lm lift Wt inj
-- statement:
--   The WGL construction uses the lm lift Wt inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftAsm.lean#L102-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftAsm.lean#L102-L108

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

theorem PI.WGL.lm_liftWt_inj {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n) {ω ω' : Fin n → ℕ}
    (he : liftWt h lam mu ω = liftWt h lam mu ω') : ω = ω' := by sorry
