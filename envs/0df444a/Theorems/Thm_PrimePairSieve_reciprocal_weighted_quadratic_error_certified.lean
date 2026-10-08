-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_weighted_quadratic_error_certified
-- name    : PrimePairSieve.reciprocal_weighted_quadratic_error_certified
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T13:18:26.108418+00:00
-- url     : https://prove2.me/theorems/b7f2cf18-0e29-4176-82fe-8a67d970e30e
-- title:
--   Finite reciprocal-weight transform with an evaluated centre and certified error factor
-- statement:
--   Let $c:\mathbb N\to\mathbb R$ with $c(0)=0$, and put $S(t)=\sum_{1\le n\le t}c(n)$. Suppose fixed real $a,b,d$ and $E\ge0$ satisfy $|S(t)-(a\log^2t+b\log t+d)|\le E t^{-1/3}$ for every $t>0$. Then, for every $z>0$,
--
--   $$\left|\sum_{1\le n\le z}\frac{c(n)}{1+n/z}-\left(a\log^2z+(b-2a\log2)\log z+d-b\log2+\frac{a\pi^2}{6}\right)\right|\le\frac{8479}{6160}E z^{-1/3}.$$
--
--   The sum uses the real cutoff, includes the endpoint and counts integers from one. This makes the reciprocal kernel estimate usable for finite arithmetic sums, with the logarithmic centre fully evaluated and all integrability conditions discharged. No sign condition on c is imposed.
-- source:
--   Adapted from cm_beta's accepted reciprocal expansion proof, submission 96ce49e2-c728-4c12-8580-1dfcf469c686, https://prove2.me/theorems/0cde8aa6-fbd7-4102-b02d-fd41125cdfc7. The evaluated logarithmic moment and tighter error factor use proved PrimePairSieve.reciprocal_log_square_kernel_integral and reciprocal_error_transfer_bound. Classical partial summation; Riesel and Vaughan, On sums of primes (1983), reciprocal weight (3.12), printed p.51, transform p.52.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve.reciprocal_weighted_quadratic_error_certified (c : ℕ → ℝ) (hc0 : c 0 = 0) (a b d E : ℝ) (hE : 0 ≤ E)
    (hbound : ∀ t : ℝ, 0 < t →
      |(∑ n ∈ Finset.Icc 1 ⌊t⌋₊, c n) -
        (a * Real.log t ^ 2 + b * Real.log t + d)| ≤ E * t ^ (-(1 / 3 : ℝ)))
    (z : ℝ) (hz : 0 < z) :
    |(∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n / (1 + (n : ℝ) / z)) -
      (a * Real.log z ^ 2 + (b - 2 * a * Real.log 2) * Real.log z +
        d - b * Real.log 2 + a * Real.pi ^ 2 / 6)| ≤
      (8479 / 6160 : ℝ) * E * z ^ (-(1 / 3 : ℝ))  := by sorry
