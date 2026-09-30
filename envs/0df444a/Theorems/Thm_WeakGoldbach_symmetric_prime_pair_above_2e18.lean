-- Prove2me | Theorems.Thm_WeakGoldbach_symmetric_prime_pair_above_2e18
-- name    : WeakGoldbach.symmetric_prime_pair_above_2e18
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-11T22:44:16.710801+00:00
-- url     : https://prove2.me/theorems/a7ac8b6d-2b3b-4d17-a782-ca0552797366
-- title:
--   Symmetric prime pairs around $m$ for $m > 2\cdot 10^{18}$
-- statement:
--   For every natural number $m > 2\cdot 10^{18}$ there exists $t \le m - 2$ such that both $m - t$ and $m + t$ are prime.
--
--   This is the symmetric form of the even Goldbach conjecture: writing $2m = (m - t) + (m + t)$ shows that it is exactly equivalent to the claim that every even $n > 4\cdot 10^{18}$ is a sum of two primes. It is the formulation targeted by symmetric-window approaches to the conjecture.
-- source:
--   Symmetric reformulation of the Goldbach conjecture; cf. the covariance-lemma reduction program (Bahbouhi, ai.viXra 2512.0013)

import Mathlib

namespace WeakGoldbach

theorem symmetric_prime_pair_above_2e18 (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    ∃ t : ℕ, t ≤ m - 2 ∧ Nat.Prime (m - t) ∧ Nat.Prime (m + t) := by
  sorry

end WeakGoldbach
