-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_log_bound_mid
-- name    : TaoFivePrimes.rosser_schoenfeld_product_log_bound_mid
-- status  : Proved
-- author  : @chstdu
-- created : 2026-09-21T17:06:18.051814+00:00
-- url     : https://prove2.me/theorems/4de11b04-b5f9-4a82-ace1-4e4dbdb6bdcc
-- title:
--   Rosser–Schoenfeld log-product bound (3.29), log form, $700 \le x \le 10^8$
-- statement:
--   For every real $x$ with $700 \le x \le 10^8$, the logarithmic form of the Rosser–Schoenfeld product bound (3.29) holds: $$\sum_{p \le \lfloor x \rfloor} \log \frac{p}{p-1} < \gamma + \log \log x + \log\left(1 + \frac{1}{2\log^2 x}\right),$$ where $\gamma$ is the Euler–Mascheroni constant. Exponentiating recovers $\prod_{p \le \lfloor x \rfloor} \frac{p}{p-1} < e^{\gamma}\log x\left(1 + \frac{1}{2\log^2 x}\right)$ on the same range. This is the middle-range leg of the reduction of `rosser_schoenfeld_product_bound`, complementing the finite verification below $700$ and the large-range bound `rosser_schoenfeld_product_log_bound_large` above $10^8$.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64–94; §8, p. 70, Theorem 8, inequality (3.29). https://doi.org/10.1215/ijm/1255631807

import Mathlib

namespace TaoFivePrimes
theorem rosser_schoenfeld_product_log_bound_mid (x : ℝ) (hx : 700 ≤ x) (hx' : x ≤ 10 ^ 8) :
    ∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log ((p : ℝ) / ((p : ℝ) - 1)) <
      Real.eulerMascheroniConstant + Real.log (Real.log x) +
        Real.log (1 + 1 / (2 * (Real.log x) ^ 2)) := by sorry
end TaoFivePrimes
