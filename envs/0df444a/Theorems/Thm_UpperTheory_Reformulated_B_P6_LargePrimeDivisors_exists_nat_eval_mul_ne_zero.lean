-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_P6_LargePrimeDivisors_exists_nat_eval_mul_ne_zero
-- name    : UpperTheory.Reformulated.B.P6.LargePrimeDivisors.exists_nat_eval_mul_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:12:23.039626+00:00
-- url     : https://prove2.me/theorems/aa3e4b5f-f386-53b7-a333-0321ce2e9aba
-- title:
--   Large Prime Divisors: exists nat eval mul ne zero
-- statement:
--   The Large Prime Divisors construction uses the exists nat eval mul ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/LargePrimeDivisors.lean#L25-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/LargePrimeDivisors.lean#L25-L36

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_LargePrimeDivisors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.LargePrimeDivisors
open scoped Int LT OfNat Polynomial Dvd

theorem UpperTheory.Reformulated.B.P6.LargePrimeDivisors.exists_nat_eval_mul_ne_zero (P : Polynomial ℤ) (hP : P ≠ 0) (a : ℤ) (ha : a ≠ 0) :
    ∃ t : ℕ, P.eval (a * (t : ℤ)) ≠ 0 := by sorry
