-- Prove2me | Theorems.Thm_PI_FinOrdRedOne_Core_eq_one_of_pow_prime
-- name    : PI.FinOrdRedOne.Core.eq_one_of_pow_prime
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:30:06.910315+00:00
-- url     : https://prove2.me/theorems/ae629308-fac8-4b42-b19c-3dfceb4507c3
-- title:
--   Core: eq one of pow prime
-- statement:
--   The Core construction uses the eq one of pow prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/EqOneOfIsOfFinOrder.lean#L118-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderReduction/EqOneOfIsOfFinOrder.lean#L118-L139

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_EqOneOfIsOfFinOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FinOrdRedOne PI.FinOrdRedOne.Core
open Matrix Finset
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

theorem PI.FinOrdRedOne.Core.eq_one_of_pow_prime [IsDomain R] (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p)
    (hp0 : (p : R) ≠ 0) (hunit : ∀ l : ℕ, l.Prime → l ≠ p → IsUnit (l : R))
    (hsep : ∀ x : R, (∀ k : ℕ, (p : R) ^ k ∣ x) → x = 0)
    (A : Matrix n n R) (hA : PDvd (p : R) 1 (A - 1)) (l : ℕ) (hl : l.Prime) (hAl : A ^ l = 1) :
    A = 1 := by sorry
