-- Prove2me | Theorems.Thm_PI_WGL_LTD_natW_sg_val
-- name    : PI.WGL.LTD.natW_sg_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:57:54.269724+00:00
-- url     : https://prove2.me/theorems/10374b9e-f40b-4023-8dd3-e99d905414d4
-- title:
--   LTD: nat W sg val
-- statement:
--   The LTD construction uses the nat W sg val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleD.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleD.lean#L18-L23

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTD
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC

theorem PI.WGL.LTD.natW_sg_val {n : ℕ} (sg : DomWeight n) (i : Fin n) :
    ((sg.natW i : ℕ) : ℤ) = sg.w i - sg.w ⟨n - 1, by have := i.2; omega⟩ := by sorry
