-- Prove2me | Theorems.Thm_PI_WGL_LTB_initMinor_std
-- name    : PI.WGL.LTB.initMinor_std
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:57:17.411214+00:00
-- url     : https://prove2.me/theorems/d8d4df9f-2f82-4f0b-9b76-4db35e019533
-- title:
--   LTB: init Minor std
-- statement:
--   The LTB construction uses the init Minor std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L25-L27

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTM

theorem PI.WGL.LTB.initMinor_std {R : Type*} [CommRing R] {r m s : ℕ} (hr : s ≤ r) (hs : s ≤ m) :
    initMinor R (n := m) (fun p : Fin s => (⟨p.1, lt_of_lt_of_le p.2 hr⟩ : Fin r)) hs = lpMinor R s hr hs := by sorry
