-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound_286_to_700
-- name    : TaoFivePrimes.rosser_schoenfeld_product_bound_286_to_700
-- status  : Proved
-- author  : @chstdu
-- created : 2026-09-21T17:06:18.353494+00:00
-- url     : https://prove2.me/theorems/78a6b8ca-0041-4695-a5af-3c881abcbfd4
-- title:
--   Rosser–Schoenfeld product bound (3.29) on $286 \le x < 700$
-- statement:
--   For every real $x$ with $286 \le x < 700$, the Rosser–Schoenfeld product bound (3.29) holds: $$\prod_{p \le \lfloor x \rfloor} \frac{p}{p-1} < e^{\gamma} \log x \left(1 + \frac{1}{2\log^2 x}\right).$$ On this short interval the claim is a finite verification: the left side is a step function constant between primes, so it suffices to check it at each prime $q \in [283, 691]$ together with the anchor $x = 286$, using exact rational certificates and Taylor bounds for $\log x$. This is the finite-range leg of the reduction of `rosser_schoenfeld_product_bound`.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64–94; §8, p. 70, Theorem 8, inequality (3.29). https://doi.org/10.1215/ijm/1255631807

import Mathlib

namespace TaoFivePrimes
theorem rosser_schoenfeld_product_bound_286_to_700 (x : ℝ) (hx : 286 ≤ x) (hx' : x < 700) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x *
        (1 + 1 / (2 * (Real.log x) ^ 2)) := by sorry
end TaoFivePrimes
