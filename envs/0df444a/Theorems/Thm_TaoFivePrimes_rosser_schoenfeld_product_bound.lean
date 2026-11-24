-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_bound
-- name    : TaoFivePrimes.rosser_schoenfeld_product_bound
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-09-17T09:14:04.069094+00:00
-- url     : https://prove2.me/theorems/fce5d444-3f09-4749-9b51-edde6aa4dae5
-- title:
--   Rosser–Schoenfeld (1962), (3.29): Mertens product upper bound
-- statement:
--   **Rosser--Schoenfeld (1962), Theorem 8, inequality (3.29).** For every real number $x \ge 286$,
--   $$\prod_{p \le x} \frac{p}{p-1} \;<\; e^{\gamma} \log x \left(1 + \frac{1}{2 \log^2 x}\right),$$
--   where the product runs over all primes $p \le \lfloor x \rfloor$ and $\gamma$ is the Euler--Mascheroni constant.
--
--   This is the explicit upper bound for the Mertens-type product $\prod_{p \le x} p/(p-1)$; equivalently, exponentiating the classical Mertens estimate $\sum_{p \le x} \log(1 - 1/p) = -\log\log x - \gamma + o(1)$, with an explicit error term valid from $x \ge 286$ on. It is inequality (3.29) of §8, Theorem 8, and is applied in §9 with $x = \log n + y - 2 \ge 286$ in the proof of Lemma 15.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64–94; §8, p. 70, Theorem 8, inequality (3.29). https://doi.org/10.1215/ijm/1255631807

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes
theorem rosser_schoenfeld_product_bound (x : ℝ) (hx : 286 ≤ x) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x *
        (1 + 1 / (2 * (Real.log x) ^ 2)) := by sorry
end TaoFivePrimes
