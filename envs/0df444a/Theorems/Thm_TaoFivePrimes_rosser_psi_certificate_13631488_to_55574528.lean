-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_psi_certificate_13631488_to_55574528
-- name    : TaoFivePrimes.rosser_psi_certificate_13631488_to_55574528
-- status  : Proved
-- author  : @BrunoDCDO
-- created : 2026-09-24T00:28:00.573605+00:00
-- url     : https://prove2.me/theorems/ab8ab35b-6c28-41d5-a553-ffa9e8631e5f
-- title:
--   Certified psi bound on (13631488, 55574528] with theta endpoint
-- statement:
--   Let $\theta(x)=\sum_{p\leq x}\log p$ and $\psi(x)=\sum_{p^m\leq x,\ m\geq1}\log p$, where $p$ ranges over primes, $m$ ranges over positive integers, and $\log$ is the natural logarithm. This finite certificate establishes
--
--   $$
--   \theta(55574528)\leq\frac{55572198560551}{1000000}
--   $$
--
--   and, for every natural number $n$ with $13631488<n\leq55574528$,
--
--   $$
--   \psi(n)<1.03883\,n.
--   $$
--
--   Both statements are unconditional. The proof obtains its initial bound for $\theta(13631488)$ from the preceding certificate and supplies a new endpoint bound for the interval above 55574528. These two conclusions allow the finite verification to continue without recomputing the earlier prime sums. The interval endpoints and rational upper bound are choices for this formal verification of the finite part of the Rosser-Schoenfeld estimate; they are not separately numbered claims in the original paper.
-- source:
--   Rosser and Schoenfeld, Approximate formulas for some functions of prime numbers (1962), Theorem 12, inequality (3.35), printed p. 71; finite-range argument on p. 77. https://doi.org/10.1215/ijm/1255631807. This certificate covers integers greater than 13631488 and at most 55574528, with a certified theta endpoint bound for composition. It uses the preceding canonical theorem TaoFivePrimes.rosser_psi_certificate_1_to_13631488 for its initial theta bound. The interval endpoints and numerical certificate are specific to this formal verification. The bit-sieve and packed-moment infrastructure is adapted with attribution from sometik179's accepted Prove2Me submission 891aecdd-2026-4fbb-9bf7-a2b4a368f347.

import Mathlib.NumberTheory.Chebyshev

theorem TaoFivePrimes.rosser_psi_certificate_13631488_to_55574528 :
    Chebyshev.theta (55574528 : ℝ) ≤ (55572198560551 : ℝ) / 1000000 ∧
    ∀ n : ℕ, 13631488 < n → n ≤ 55574528 →
      Chebyshev.psi (n : ℝ) < 1.03883 * (n : ℝ) := by sorry
