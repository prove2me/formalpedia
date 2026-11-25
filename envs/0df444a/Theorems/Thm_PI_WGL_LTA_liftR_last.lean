-- Prove2me | Theorems.Thm_PI_WGL_LTA_liftR_last
-- name    : PI.WGL.LTA.liftR_last
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:46:22.196842+00:00
-- url     : https://prove2.me/theorems/9a7c987b-a0a0-4988-bfca-d6f13a32f744
-- title:
--   LTA: lift R last
-- statement:
--   The LTA construction uses the lift R last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleA.lean#L135-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleA.lean#L135-L137

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTA
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem PI.WGL.LTA.liftR_last {r n m : ℕ} (e : Fin n → Fin r) (z : Fin r) (ρ : Fin m → Fin n) :
    liftR e z ρ (Fin.last m) = z := by sorry
