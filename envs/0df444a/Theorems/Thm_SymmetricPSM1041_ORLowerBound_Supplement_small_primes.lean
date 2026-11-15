-- Prove2me | Theorems.Thm_SymmetricPSM1041_ORLowerBound_Supplement_small_primes
-- name    : SymmetricPSM1041.ORLowerBound.Supplement.small_primes
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:50:48.899564+00:00
-- url     : https://prove2.me/theorems/7ff35fa5-8373-499d-9c85-2439fbebb57a
-- title:
--   Lemma 39 — small primes with large product
-- statement:
--   There are constants $C$, $j$ and $N\ge1$ such that for every $n\ge N$ there are distinct primes $p_1,\dots,p_k$ with $Q=\max_i p_i$ such that
--
--   1. $p_1\cdots p_k>n$,
--   2. $Q^k\le C\,n\log_2^3 n$,
--   3. $k\le C\log_2^j n$ and $Q\le C\log_2^j n$.
--
--   This is the source's $Q^k=O(n\log^3n)$ and $k,Q=\mathrm{polylog}(n)$. The primes are the moduli used to reconstruct the Hamming weight in the protocols of Theorems 31 and 32.
--
--   **Formalization Note** The primes form a finite set of naturals (so they are distinct); $Q$ is its supremum, which is the maximum since the product exceeds $n\ge1$ and the set is nonempty.
--
--   Differences from the source:
--   - encoding: Q^k = O(n log³ n) and k, Q = polylog(n), for all sufficiently large n → one C, one exponent j, one N with Q^k ≤ C n (log₂ n)³, k ≤ C (log₂ n)^j, Q ≤ C (log₂ n)^j for all n ≥ N; reason: taking the maximum of the constants and exponents of the separate O- and polylog-bounds gives a common C and j
-- source:
--   Marshall Ball, Peter Crawford-Kahrl, Vladimir Podolskii, Morgan Prior, STOC 2027 submission #1041 (October 2026), p. 27, Lemma 39 (proof pp. 27–28)

import Mathlib

namespace SymmetricPSM1041.ORLowerBound.Supplement

theorem small_primes :
    ∃ C : ℝ, ∃ j : ℕ, ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      ∃ Ps : Finset ℕ, (∀ p ∈ Ps, p.Prime) ∧ n < ∏ p ∈ Ps, p ∧
        ((Ps.sup id : ℕ) : ℝ) ^ Ps.card ≤ C * (n : ℝ) * (Real.logb 2 n) ^ 3 ∧
        (Ps.card : ℝ) ≤ C * (Real.logb 2 n) ^ j ∧
        ((Ps.sup id : ℕ) : ℝ) ≤ C * (Real.logb 2 n) ^ j := by sorry

end SymmetricPSM1041.ORLowerBound.Supplement
