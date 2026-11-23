-- Prove2me | Theorems.Thm_PI_WGL_LTE_aLast_val
-- name    : PI.WGL.LTE.aLast_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:57:59.202346+00:00
-- url     : https://prove2.me/theorems/5dbf4c02-5d95-413e-8a7f-0374708fc6b4
-- title:
--   LTE: a Last val
-- statement:
--   The LTE construction uses the a Last val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleE.lean#L117-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleE.lean#L117-L124

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTE
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD

theorem PI.WGL.LTE.aLast_val {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    (hn : 0 < n) :
    (((aa h lam sg ⟨n - 1, by omega⟩).toNat : ℕ) : ℤ) = sg.w ⟨n - 1, by omega⟩ - lam.w ⟨n, by omega⟩ := by sorry
