-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_4500_to_5000
-- name    : TaoFivePrimes.rosser_schoenfeld_product_bound_4500_to_5000
-- status  : Proved
-- author  : @chstdu
-- created : 2026-09-23T10:36:56.783621+00:00
-- url     : https://prove2.me/theorems/e923bcfe-08c5-4f25-a1b1-afbdb14dd782
-- title:
--   Rosser–Schoenfeld product bound, range $4500 \le x \le 5000$
-- statement:
--   For every real number $x$ with $4500 \le x \le 5000$,
--   $$\prod_{p \le x, \; p \text{ prime}} \frac{p}{p-1} < e^{\gamma} \log x + \frac{2e^{\gamma}}{\sqrt{x}},$$
--   where the product runs over the primes $p \le x$ and $\gamma$ denotes the Euler–Mascheroni constant.
--
--   This is a finite-range leg of the upper-bound part of Rosser–Schoenfeld's
--   explicit Mertens product estimate. The range $[4500, 5000]$ continues the
--   certified ladder of legs ($[505,700], [700,1500], \dots, [4000,4500]$) towards
--   the analytic régime $x \ge 10^8$, where the bound follows from
--   Schoenfeld's estimate for $\vartheta(x)$ instead. The leg is a pure
--   finite verification: anchored at the primorial certificate for the
--   checkpoint prime $4493$ (the largest prime $\le 4500$), the product
--   $\prod_{p \le x} p/(p-1)$ is tracked at each of the $60$ primes up to
--   $4999$ by exact rational arithmetic, and the two competing sides are
--   compared via certified decimal intervals for $e^{\gamma}$, $e$ and $\log$.
-- source:
--   Rosser–Schoenfeld 1962, Approximate formulas for some functions of prime numbers, §3 (explicit Mertens product bound); finite range verification by exact rational arithmetic.

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes
theorem rosser_schoenfeld_product_bound_4500_to_5000 (x : ℝ) (hx : 4500 ≤ x) (hx' : x ≤ 5000) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by sorry
end TaoFivePrimes
