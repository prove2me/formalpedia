-- Prove2me | Theorems.Thm_PI_WGL_LTB_count_succ
-- name    : PI.WGL.LTB.count_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:58:27.192625+00:00
-- url     : https://prove2.me/theorems/735df2bc-92b3-48b7-bd67-b3e512d5fcfb
-- title:
--   LTB: count succ
-- statement:
--   The LTB construction uses the count succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L204-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L204-L226

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

theorem PI.WGL.LTB.count_succ {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (s : Fin n) :
    (Finset.univ.filter fun k => sz k = s.1 + 1).card = shapeDeg sz s - nuNext (shapeDeg sz) s := by sorry
