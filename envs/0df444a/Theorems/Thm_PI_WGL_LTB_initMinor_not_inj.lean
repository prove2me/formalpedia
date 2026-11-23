-- Prove2me | Theorems.Thm_PI_WGL_LTB_initMinor_not_inj
-- name    : PI.WGL.LTB.initMinor_not_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:08:26.373804+00:00
-- url     : https://prove2.me/theorems/0fca5753-11a0-43ad-9feb-463c7ccbc15d
-- title:
--   LTB: init Minor not inj
-- statement:
--   The LTB construction uses the init Minor not inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L17-L23

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

theorem PI.WGL.LTB.initMinor_not_inj {R : Type*} [CommRing R] {r m s : ℕ} (I : Fin s → Fin r) (hs : s ≤ m)
    (hI : ¬ Function.Injective I) : initMinor R (n := m) I hs = 0 := by sorry
