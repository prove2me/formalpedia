-- Prove2me | Theorems.Thm_TaoFivePrimes_vonMangoldt_series_split_at_threshold_of_zero
-- name    : TaoFivePrimes.vonMangoldt_series_split_at_threshold_of_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T15:33:30.582409+00:00
-- url     : https://prove2.me/theorems/460cd53e-37ca-4d6d-9f77-523481e6a7df
-- title:
--   Vaughan's two-range split of a von Mangoldt weighted series, corrected to support in the positive naturals
-- statement:
--   Vaughan's two-range split of a von Mangoldt weighted series, corrected so
--   that `f` is supported in the positive natural numbers.
--
--   Assume `f : N -> C` has finite support and `f 0 = 0`.  Then for every threshold `U`,
--
--     sum_n Lambda(n) f(n)
--       = sum_{d <= U}  -mu(d) log(d) sum_m f(d m)
--       + sum_{d >  U}  -mu(d) log(d) sum_m f(d m).
--
--   The two ranges partition the divisors, so the right-hand side is the left-hand side
--   written in two pieces.
--
--   Why `f 0 = 0` is required.  The originally published statement
--   `TaoFivePrimes.vonMangoldt_series_split_at_threshold` assumed only finite support, and
--   is false.  For `d > N0` every `m >= 1` has `d * m > N0` so `f (d * m) = 0`, but the
--   `m = 0` term is `f 0`, which was unconstrained.  The outer summand is then
--   `-mu(d) log(d) * f 0`, and `sum_d |mu d| log d` diverges because it dominates
--   `sum_p log p`.  Mathlib's `tsum` is `0` for a non-summable family, so the right-hand
--   side collapses to `0`, while the left-hand side is the nonzero finite sum
--   `sum_{n=1}^{N0} Λ(n) f(n)`.
--
--   Why it holds with `f 0 = 0`.  The pointwise identity is
--   `sum_{d | n} mu(d) log(d) = -Lambda(n)`, i.e. Mathlib's `[simp]` theorem
--   `moebius_mul_log_eq_vonMangoldt : (mu : ArithmeticFunction R) * log = vonMangoldt`.
--   Summing that against `f n` and reindexing by `n = d * m` turns the divisor sum into a
--   sum over `d` and `m`.  With `f 0 = 0` the inner `m`-sum is supported on
--   `{m : d * m <= N0}`, hence vanishes for `d > N0`, so the whole right-hand side is a
--   finite rearrangement that Lean can verify directly.  Splitting the outer `d` sum at
--   `U` gives the two ranges.
--
--   Role in the five-primes proof.  This is the structural input to Proposition 7.2 of Tao,
--   *Most odd numbers are sums of four primes* (arXiv:1201.6656): the small-divisor range is
--   estimated by a truncated Poisson summation whose error is exactly the zeta zero count
--   below `T_0 = 3.29e9`, and the large-divisor range is bounded directly.
--   `TaoFivePrimes.major_arc_sums_positive_scale` carries the resulting analytic
--   estimates.
-- source:
--   Tao, Most odd numbers are sums of four primes, arXiv:1201.6656, Section 7; minimal correction of TaoFivePrimes.vonMangoldt_series_split_at_threshold (d280ed90-254c-4d0c-8cb7-89487d7de898), which is false without f 0 = 0

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

namespace TaoFivePrimes
/-- Vaughan's two-range split of a von Mangoldt weighted series, with support in the
positive natural numbers.

This is `TaoFivePrimes.vonMangoldt_series_split_at_threshold` with the minimal
correction `f 0 = 0`.  Without that hypothesis the published statement is false: for
`d > N0` the inner sum `∑' m, f (d * m)` retains its `m = 0` term `f 0`, so the outer
summand is `-mu d log d * f 0`, and `∑_d |mu d| log d` diverges (it dominates
`∑_p log p`).  Mathlib's `tsum` is defined to be `0` for a non-summable family
(`tsum_eq_zero_of_not_summable`), so the right-hand side collapses to `0`, while the
left-hand side is the nonzero finite sum `∑_{n=1}^{N0} Λ n f n`.

With `f 0 = 0` every inner sum is supported on `{m : d * m ≤ N0}`, hence vanishes for
`d > N0`, so the right-hand side is a finite sum that Lean can verify directly. -/
theorem vonMangoldt_series_split_at_threshold_of_zero (f : ℕ → ℂ) (U : ℕ)
    (hfin : Exists fun N0 : ℕ => forall n : ℕ, N0 < n -> f n = 0) (hf0 : f 0 = 0) :
    (∑' n : ℕ, ((Λ n : ℝ) : ℂ) * f n) =
      (∑' d : ℕ, (if d <= U then 1 else 0) * (-((((μ d : ℤ) : ℝ) : ℂ) * Real.log d)) *
        (∑' m : ℕ, f (d * m))) +
      (∑' d : ℕ, (if U < d then 1 else 0) * (-((((μ d : ℤ) : ℝ) : ℂ) * Real.log d)) *
        (∑' m : ℕ, f (d * m))) := by
  sorry

end TaoFivePrimes
