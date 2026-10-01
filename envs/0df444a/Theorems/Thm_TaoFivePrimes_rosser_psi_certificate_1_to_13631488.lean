-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_psi_certificate_1_to_13631488
-- name    : TaoFivePrimes.rosser_psi_certificate_1_to_13631488
-- status  : Proved
-- author  : @BrunoDCDO
-- created : 2026-09-24T00:21:45.376448+00:00
-- url     : https://prove2.me/theorems/71ee979a-0b89-4347-bd34-863d90f4d2f2
-- title:
--   Certified psi bound up to 13,631,488 with theta endpoint
-- statement:
--   Let $\theta(x)=\sum_{p\leq x}\log p$ and $\psi(x)=\sum_{p^m\leq x,\ m\geq1}\log p$, where $p$ ranges over primes and $m$ over positive integers. This finite certificate establishes
--
--   $$
--   \theta(13631488)\leq\frac{13628933774400}{1000000}
--   $$
--
--   and, for every integer $n$ with $1000<n\leq13631488$,
--
--   $$
--   \psi(n)<1.03883\,n.
--   $$
--
--   The endpoint estimate supplies the initial upper bound for $\theta$ in the next contiguous interval. Both statements are unconditional. The endpoints and the rational upper bound are chosen for this formal verification of the finite part of the Rosser-Schoenfeld estimate; they are not separately numbered claims in the original paper. This certificate alone does not cover integers above 13631488.
-- source:
--   Rosser and Schoenfeld, Approximate formulas for some functions of prime numbers (1962), Theorem 12, inequality (3.35), printed p. 71; finite-range argument on p. 77. https://doi.org/10.1215/ijm/1255631807. This is a new finite certificate for a subinterval of that estimate, with an additional certified theta endpoint bound for composition. Its interval endpoints and numerical certificate are specific to this formal verification. The bit-sieve infrastructure is adapted with attribution from sometik179's accepted Prove2Me submission 891aecdd-2026-4fbb-9bf7-a2b4a368f347.

import Mathlib.NumberTheory.Chebyshev

theorem TaoFivePrimes.rosser_psi_certificate_1_to_13631488 :
    Chebyshev.theta (13631488 : ℝ) ≤ (13628933774400 : ℝ) / 1000000 ∧
    ∀ n : ℕ, 1000 < n → n ≤ 13631488 →
      Chebyshev.psi (n : ℝ) < 1.03883 * (n : ℝ) := by sorry
