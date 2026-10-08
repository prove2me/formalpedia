-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_weight_factor_certificate_sound
-- name    : PrimePairSieve.reciprocal_weight_factor_certificate_sound
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T17:20:11.348345+00:00
-- url     : https://prove2.me/theorems/dce0d411-d2e1-42cd-a9d6-30758a1408c5
-- title:
--   Soundness of reciprocal weight factor certificates
-- statement:
--   This lemma validates a kernel-checkable prime-factor certificate for sparse reciprocal-sieve tables.
--
--   Given a natural number `n` and a finite set `s` of primes, the predicate `reciprocal_weight_check n s` is true exactly when every element of `s` is prime and the product of `s` equals `n`. The theorem shows that any such certificate implies `n` is squarefree and `n.primeFactors = s`.
--
--   The proof is pure finite arithmetic: decode the boolean with `of_decide_eq_true`, then use pairwise coprimality of distinct primes and `Nat.primeFactors_prod`.
-- source:
--   Prove2Me five-primes finite-window certificate design (2026-10-04)

import Mathlib
import Definitions.Def_PrimePairSieve_reciprocal_weight_check
open scoped BigOperators
set_option autoImplicit false

namespace PrimePairSieve

theorem reciprocal_weight_factor_certificate_sound (n : ℕ) (s : Finset ℕ)
    (hcheck : reciprocal_weight_check n s = true) :
    Squarefree n ∧ n.primeFactors = s := by sorry

end PrimePairSieve
