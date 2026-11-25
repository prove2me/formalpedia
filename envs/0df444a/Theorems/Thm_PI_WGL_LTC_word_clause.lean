-- Prove2me | Theorems.Thm_PI_WGL_LTC_word_clause
-- name    : PI.WGL.LTC.word_clause
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:43:41.667412+00:00
-- url     : https://prove2.me/theorems/a8a89a35-2ec0-483b-9e20-43fd9169ff33
-- title:
--   LTC: word clause
-- statement:
--   The LTC construction uses the word clause property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleC.lean#L95-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GelfandTsetlinLowering/LiftTupleC.lean#L95-L120

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

theorem PI.WGL.LTC.word_clause {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) {K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (L : Finset (Fin K)) (I : ∀ k, Fin (sz k) → Fin n)
    (w : List (Fin n × Fin n × ℕ)) (hw : OffDiag w) :
    ∃ d : (∀ k, Fin (sz k) → Fin n) →₀ ℤ,
      applyWord ℤ w (bideterminant ℤ sz hsz I) = d.sum (fun J c => c • bideterminant ℤ sz hsz J) ∧
      applyWord ℤ (liftWord h w) (Mlift h lam sg sz hsz L I) =
        d.sum (fun J c => c • Mlift h lam sg sz hsz L J) := by sorry
