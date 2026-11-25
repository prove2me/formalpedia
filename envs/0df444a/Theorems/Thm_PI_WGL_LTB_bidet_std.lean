-- Prove2me | Theorems.Thm_PI_WGL_LTB_bidet_std
-- name    : PI.WGL.LTB.bidet_std
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:47:05.497794+00:00
-- url     : https://prove2.me/theorems/c1f2e33e-2063-4e36-ac62-2beace87008f
-- title:
--   LTB: bidet std
-- statement:
--   The LTB construction uses the bidet std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L228-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L228-L249

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

theorem PI.WGL.LTB.bidet_std {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (ν : Fin n → ℕ) (hsh : shapeDeg sz = ν) :
    bideterminant ℤ sz hsz (stdT sz hsz) = hw ℤ (r := n) le_rfl ν := by sorry
