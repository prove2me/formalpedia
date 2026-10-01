-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_psi_certificate_55574528_to_100000000
-- name    : TaoFivePrimes.rosser_psi_certificate_55574528_to_100000000
-- status  : Proved
-- author  : @BrunoDCDO
-- created : 2026-09-24T00:28:02.396452+00:00
-- url     : https://prove2.me/theorems/ed51c6ce-668f-4e90-9b27-c7e653bf8050
-- title:
--   Certified psi bound on (55574528, 100000000] with theta endpoint
-- statement:
--   Let $\theta(x)=\sum_{p\leq x}\log p$ and $\psi(x)=\sum_{p^m\leq x,\ m\geq1}\log p$, where $p$ ranges over primes, $m$ ranges over positive integers, and $\log$ is the natural logarithm. This finite certificate establishes
--
--   $$
--   \theta(100000000)\leq\frac{100001502370081}{1000000}
--   $$
--
--   and, for every natural number $n$ with $55574528<n\leq100000000$,
--
--   $$
--   \psi(n)<1.03883\,n.
--   $$
--
--   Both statements are unconditional. The proof obtains its initial bound for $\theta(55574528)$ from the preceding certificate. This final interval includes $10^8$ and, together with the preceding two intervals, covers the finite obligation $1000<n<10^8$. The endpoint bound records the cumulative estimate for $\theta$ at the end of the certificate. The interval endpoints and rational upper bound are choices for this formal verification; the separate infinite-range estimate remains outside its scope.
-- source:
--   Rosser and Schoenfeld, Approximate formulas for some functions of prime numbers (1962), Theorem 12, inequality (3.35), printed p. 71; finite-range argument on p. 77. https://doi.org/10.1215/ijm/1255631807. This certificate covers integers greater than 55574528 and at most 100000000, and records the final certified theta endpoint bound. It uses the preceding canonical theorem TaoFivePrimes.rosser_psi_certificate_13631488_to_55574528 for its initial theta bound. Together with the preceding two certificates, it covers every integer strictly between 1000 and 100000000. The interval endpoints and numerical certificate are specific to this formal verification. The bit-sieve and packed-moment infrastructure is adapted with attribution from sometik179's accepted Prove2Me submission 891aecdd-2026-4fbb-9bf7-a2b4a368f347.

import Mathlib.NumberTheory.Chebyshev

theorem TaoFivePrimes.rosser_psi_certificate_55574528_to_100000000 :
    Chebyshev.theta (100000000 : ℝ) ≤ (100001502370081 : ℝ) / 1000000 ∧
    ∀ n : ℕ, 55574528 < n → n ≤ 100000000 →
      Chebyshev.psi (n : ℝ) < 1.03883 * (n : ℝ) := by sorry
