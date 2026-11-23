-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_P6_LargePrimeDivisors_GlobalTheory_CompanionTheory_Hypotheses__Shintani_exists_large_prime_dvd_eval_8fd8b0229643
-- name    : P2M_UpperTheory_Reformulated_B_P6_LargePrimeDivisors_GlobalTheory_CompanionTheory_Hypotheses__Shintani_exists_large_prime_dvd_eval_8fd8b0229643
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:12.235075+00:00
-- url     : https://prove2.me/theorems/1a4a4a4d-55a9-4091-8518-5757d6b5ae43
-- title:
--   P2 M Upper Theory Reformulated B P6 Large Prime Divisors Global Theory Companion Theory Hypotheses  Shintani exists large prime dvd eval 8fd8b0229643: P2 M Upper Theory Reformulated B P6 Large Prime D
-- statement:
--   The P2 M Upper Theory Reformulated B P6 Large Prime Divisors Global Theory Companion Theory Hypotheses  Shintani exists large prime dvd eval 8fd8b0229643 construction uses the P2 M Upper Theory Reformulated B P6 Large Prime Divisors Global Theory Companion Theory Hypotheses  Shintani exists large prime dvd eval 8fd8b0229643 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/LargePrimeDivisors.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/LargePrimeDivisors.lean#L97-L100

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

theorem P2M_UpperTheory_Reformulated_B_P6_LargePrimeDivisors_GlobalTheory_CompanionTheory_Hypotheses__Shintani_exists_large_prime_dvd_eval_8fd8b0229643 :
    ∀ (f : Polynomial ℤ), OfNat.ofNat (nat_lit 0) < f.natDegree → ∀ (N : ℕ), ∃ (p : ℕ) (m : ℤ), Nat.Prime p ∧ N < p ∧ p.cast ∣ Polynomial.eval m f := by sorry

alias «UpperTheory».«Reformulated».«B».«P6».«LargePrimeDivisors».«GlobalTheory».«CompanionTheory».«Hypotheses₂».«Shintani».«exists_large_prime_dvd_eval» := P2M_UpperTheory_Reformulated_B_P6_LargePrimeDivisors_GlobalTheory_CompanionTheory_Hypotheses__Shintani_exists_large_prime_dvd_eval_8fd8b0229643
