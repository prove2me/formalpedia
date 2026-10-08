-- Prove2me | Theorems.Thm_PrimePairSieve_sparse_selected_prime_factor_bound
-- name    : PrimePairSieve.sparse_selected_prime_factor_bound
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T16:29:07.809979+00:00
-- url     : https://prove2.me/theorems/fd3ee43f-f6ac-427b-9678-be6b46038195
-- title:
--   Sparse reciprocal weights force small prime factors
-- statement:
--   Suppose a squarefree index $n$ has literal reciprocal sieve weight $w(n)\ge 1/K$ for a positive integer $K$. Then every prime factor $p$ of $n$ satisfies $p\le 4K+2$.
-- source:
--   Prove2Me five-primes reciprocal finite-window certificate design note (2026-10-04)

import Mathlib
import Definitions.Def_PrimePairSieve_ReciprocalLiteralWeight
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve.sparse_selected_prime_factor_bound (n p K : ℕ) (hK : 0 < K)
    (hselected : (1 : ℝ) / K ≤ PrimePairSieve.reciprocal_literal_weight n)
    (hp : p ∈ n.primeFactors) :
    p ≤ 4 * K + 2 := by sorry
