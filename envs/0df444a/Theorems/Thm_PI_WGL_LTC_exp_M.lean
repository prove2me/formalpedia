-- Prove2me | Theorems.Thm_PI_WGL_LTC_exp_M
-- name    : PI.WGL.LTC.exp_M
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:50:44.108574+00:00
-- url     : https://prove2.me/theorems/21a61d99-0281-4e97-ba58-6cf7b90b125d
-- title:
--   LTC: exp M
-- statement:
--   The LTC construction uses the exp M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleC.lean#L26-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleC.lean#L26-L36

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTC
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM

theorem PI.WGL.LTC.exp_M {n N : ℕ} (h : n + 1 = N) {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (L : Finset (Fin K))
    (k : Fin K) :
    Exp (eRow h) (fun ρ : Fin (sz k) → Fin n =>
      if k ∈ L then lif h ρ (by have := hsz k; omega) else unl h ρ (by have := hsz k; omega)) := by sorry
