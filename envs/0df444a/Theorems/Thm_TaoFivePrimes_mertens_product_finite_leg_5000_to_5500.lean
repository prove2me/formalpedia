-- Prove2me | Theorems.Thm_TaoFivePrimes_mertens_product_finite_leg_5000_to_5500
-- name    : TaoFivePrimes.mertens_product_finite_leg_5000_to_5500
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-23T17:48:47.020363+00:00
-- url     : https://prove2.me/theorems/e0b776e9-02d1-4f25-ad86-c2a9e18fabf9
-- title:
--   Mertens product bound on the finite leg [5000, 5500]: exact rational walk from the 4999 primorial certificate
-- statement:
--   ## Statement
--
--   For every real number $x$ with $5000 \le x \le 5500$,
--   $$\prod_{p \le x, \; p \text{ prime}} \frac{p}{p-1} < e^{\gamma} \log x + \frac{2e^{\gamma}}{\sqrt{x}},$$
--   where the product runs over the primes $p \le x$ and $\gamma$ denotes the Euler–Mascheroni constant.
--
--   ## Meaning
--
--   This is the first finite leg of the decomposition of
--   `TaoFivePrimes.rosser_schoenfeld_product_bound_5000_to_1e8`
--   (theorem 41877d9e-61fc-4fe8-ba5c-e031826409c4, status Open, deprecated_at null),
--   whose natural-language statement describes the expected proof split: a finite leg
--   $[5000, 5500]$ followed by the analytic tail $[5500, 10^8]$. It extends the certified
--   finite legs below $5000$ ($[505,700]$, $\dots$, $[4500,5000]$) by one rung.
--
--   ## Proof route
--
--   Pure finite computation. The left-hand side is piecewise constant: it changes only at
--   the finitely many primes in $[5000, 5500]$, while the right-hand side is strictly
--   increasing in $x$. It therefore suffices to check the inequality at the left endpoint
--   $x = p$ of each jump interval — an exact rational walk: the product at each step is an
--   exact rational, and the right-hand side at each prime admits rigorous rational bounds
--   (rational bounds for $e^{\gamma}$, $\log p$, $\sqrt{p}$, in the style of
--   `PrimePairSieve.sieve_constants_certificate`), anchored at the primorial certificate
--   for $4999$. Decidable; no analysis required.
-- source:
--   Five-primes mission; finite leg [5000,5500] of TaoFivePrimes.rosser_schoenfeld_product_bound_5000_to_1e8 (41877d9e-61fc-4fe8-ba5c-e031826409c4, live-verified Open + deprecated_at null 2026-09-24). The parent's own natural-language statement describes this split. Reference: Rosser–Schoenfeld 1962, Approximate formulas for some functions of prime numbers, §3.

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

set_option autoImplicit false

namespace TaoFivePrimes

theorem mertens_product_finite_leg_5000_to_5500 (x : ℝ) (hx : 5000 ≤ x) (hx' : x ≤ 5500) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by sorry

end TaoFivePrimes
