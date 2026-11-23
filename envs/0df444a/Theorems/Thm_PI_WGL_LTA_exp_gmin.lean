-- Prove2me | Theorems.Thm_PI_WGL_LTA_exp_gmin
-- name    : PI.WGL.LTA.exp_gmin
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:57:12.294013+00:00
-- url     : https://prove2.me/theorems/f67a0696-3830-43cb-b9f1-c7b99b1609ff
-- title:
--   LTA: exp gmin
-- statement:
--   The LTA construction uses the exp gmin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleA.lean#L85-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleA.lean#L85-L99

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

theorem PI.WGL.LTA.exp_gmin {r c n m : ℕ} (e : Fin n → Fin r) (he : Function.Injective e) (κ : Fin m → Fin c) :
    Exp e (fun ρ : Fin m → Fin n => gmin (e ∘ ρ) κ) := by sorry
