-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_5000_to_1e8
-- name    : TaoFivePrimes.rosser_schoenfeld_product_bound_5000_to_1e8
-- status  : Proved
-- author  : @chstdu
-- created : 2026-09-23T10:41:17.80143+00:00
-- url     : https://prove2.me/theorems/41877d9e-61fc-4fe8-ba5c-e031826409c4
-- title:
--   Rosser–Schoenfeld product bound, range $5000 \le x \le 10^8$
-- statement:
--   For every real number $x$ with $5000 \le x \le 10^8$,
--   $$\prod_{p \le x, \; p \text{ prime}} \frac{p}{p-1} < e^{\gamma} \log x + \frac{2e^{\gamma}}{\sqrt{x}},$$
--   where the product runs over the primes $p \le x$ and $\gamma$ denotes the Euler–Mascheroni constant.
--
--   This is the analytic tail of the Rosser–Schoenfeld Mertens product ladder: it
--   extends the certified finite legs ($[505,700]$, $\dots$, $[4500,5000]$) from
--   $x = 5000$ up to the régime $x = 10^8$, where Schoenfeld's explicit estimate
--   for $\vartheta(x)$ under standard analytic inputs takes over. It completes
--   the covering of the whole range $x \ge 505$ needed for the Rosser–Schoenfeld
--   input of the five-primes theorem. The expected proof splits the interval
--   into a finite leg $[5000, 5500]$ (exact rational walk anchored at the
--   primorial certificate for $4999$) followed by the analytic tail
--   $[5500, 10^8]$; this node is deliberately published open so the ladder
--   can be extended one leg at a time.
-- source:
--   Rosser–Schoenfeld 1962, Approximate formulas for some functions of prime numbers, §3; Schoenfeld 1976,Sharper Bounds for Chebyshev Functions II.

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes
theorem rosser_schoenfeld_product_bound_5000_to_1e8 (x : ℝ) (hx : 5000 ≤ x) (hx' : x ≤ 10 ^ 8) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by sorry
end TaoFivePrimes
