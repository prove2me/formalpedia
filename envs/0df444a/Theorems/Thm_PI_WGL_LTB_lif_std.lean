-- Prove2me | Theorems.Thm_PI_WGL_LTB_lif_std
-- name    : PI.WGL.LTB.lif_std
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:46:47.269015+00:00
-- url     : https://prove2.me/theorems/f5467ec1-ae8c-4b54-89bd-3e1f852f4887
-- title:
--   LTB: lif std
-- statement:
--   The LTB construction uses the lif std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L279-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleB.lean#L279-L287

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

theorem PI.WGL.LTB.lif_std {n N : ℕ} (h : n + 1 = N) {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (k : Fin K)
    (hk : sz k < n) (hm : sz k + 1 ≤ N) :
    lif h (stdT sz hsz k) hm = initMinor ℤ (n := N) (rowsZ h ⟨sz k, hk⟩) hm := by sorry
