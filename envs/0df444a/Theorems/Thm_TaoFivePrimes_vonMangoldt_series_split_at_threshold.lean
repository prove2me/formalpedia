-- Prove2me | Theorems.Thm_TaoFivePrimes_vonMangoldt_series_split_at_threshold
-- name    : TaoFivePrimes.vonMangoldt_series_split_at_threshold
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-05T14:06:04.299995+00:00
-- url     : https://prove2.me/theorems/d280ed90-254c-4d0c-8cb7-89487d7de898
-- title:
--   Vaughan's two-range split of a von Mangoldt weighted series at any divisor threshold (Tao, arXiv:1201.6656, Section 7)
-- statement:
--   Vaughan's two-range split of a von Mangoldt weighted series.  Assume `f : N -> C` has finite
--   support, so that all sums below are finite.  Then for every threshold `U`,
--
--     sum_n Lambda(n) f(n)
--       = sum_{d <= U}  -mu(d) log(d) sum_m f(d m)
--       + sum_{d >  U}  -mu(d) log(d) sum_m f(d m).
--
--   The two ranges partition the divisors, so the right-hand side is the left-hand side written
--   in two pieces.
--
--   Why it holds.  The pointwise identity is `sum_{d | n} mu(d) log(d) = -Lambda(n)` for `n >= 1`,
--   which in Mathlib is the `[simp]` theorem `moebius_mul_log_eq_vonMangoldt : (mu : ArithmeticFunction R) * log
--   = vonMangoldt`.  Summing that against `f n` and reindexing by `n = d * m` turns the divisor sum into
--   a sum over `d` and `m`; splitting that outer `d` sum at `U` gives the two ranges.
--
--   Role in the five-primes proof.  Proposition 7.2 of Tao, *Most odd numbers are sums of four
--   primes* (arXiv:1201.6656), bounds the major arc sum `S_{eta,1}(x, alpha)` against the archimedean
--   integral `x * int eta(y) e(alpha x y) dy`, with an error controlled by the number of zeta zeroes
--   below `T_0 = 3.29e9`.  This split is the structural input: the small-divisor range is estimated by
--   a truncated Poisson summation whose error is exactly the zero count, while the large-divisor range
--   is bounded directly.  `TaoFivePrimes.major_arc_sums_positive_scale` is the resulting statement.
--
--   Formulation notes.  This is stated for a general finitely supported `f` rather than directly for
--   `smoothedExpSum eta 1 x alpha`.  At `q_0 = 1` the coprimality guard in `smoothedExpSum` is vacuous, so
--   the smoothed case is exactly this statement with `f n = expCircle (alpha * n) * eta ((n : R) / x)`,
--   which has finite support because `eta` is compactly supported.  Finite support is what makes this a
--   finite rearrangement that can be verified directly, rather than an infinite-series identity whose
--   convergence would have to be established before the rearrangement is even meaningful.
--
--   The threshold `U` is left as a parameter because the usable content of Proposition 7.2 is precisely
--   that one may take `U` comparable to `sqrt x` while keeping both ranges under control; a later
--   statement fixes that choice and carries the analytic estimates.
-- source:
--   Tao, Most odd numbers are sums of four primes, arXiv:1201.6656, Section 7; pointwise identity from Mathlib ArithmeticFunction.sum_moebius_mul_log_eq

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

namespace TaoFivePrimes
/-- Vaughan's two-range split of a von Mangoldt weighted series.

For `f` of finite support and any threshold `U`, the series splits at `U`:

    sum' n, (Λ n : C) * f n
      = (small-divisor range over d with d <= U)
        + (large-divisor range over d with U < d)

each range weighted by `-mu d * log d` and summing `f (d * m)` over `m`. The
pointwise identity is Mathlib's `sum_moebius_mul_log_eq`. -/
theorem vonMangoldt_series_split_at_threshold (f : ℕ → ℂ) (U : ℕ)
    (hfin : Exists fun N0 : ℕ => forall n : ℕ, N0 < n -> f n = 0) :
    (∑' n : ℕ, ((Λ n : ℝ) : ℂ) * f n) =
      (∑' d : ℕ, (if d <= U then 1 else 0) * (-((((μ d : ℤ) : ℝ) : ℂ) * Real.log d)) *
        (∑' m : ℕ, f (d * m))) +
      (∑' d : ℕ, (if U < d then 1 else 0) * (-((((μ d : ℤ) : ℝ) : ℂ) * Real.log d)) *
        (∑' m : ℕ, f (d * m))) := by
  sorry

end TaoFivePrimes
