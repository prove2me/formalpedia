-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_bound
-- name    : TaoFivePrimes.rosser_schoenfeld_totient_bound
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-09-17T06:55:02.62056+00:00
-- url     : https://prove2.me/theorems/13e6ac07-8b76-4b45-b23d-65aa8490a64b
-- title:
--   Rosser–Schoenfeld totient bound in Tao's uniform form
-- statement:
--   Let $H \ge 100$ and let $n$ be odd with $1 \le n \le H$. Then
--   $$\frac{2n}{\varphi(2n)} \;\le\; e^{\gamma} \log\log(2H) \;+\; \frac{2.507}{\log\log(2H)},$$
--   where $\varphi$ is Euler's totient function and $\gamma$ is the Euler–Mascheroni constant. This is Rosser–Schoenfeld Theorem 15 in the uniform form derived by Tao in the proof of Proposition 4.10: pointwise at $2n$ the theorem is weaker than the value at $2H$ only for the three small cases $n = 1, 3, 5$, which are verified by hand, as in Tao's proof.
-- source:
--   J. B. Rosser, L. Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois Journal of Mathematics 6 (1962), 64–94, Theorem 15; uniform form in T. Tao, *Every odd number greater than 1 is the sum of at most five primes*, arXiv:1201.6656, https://arxiv.org/abs/1201.6656, proof of Proposition 4.10.

import Definitions.Def_TaoFivePrimes_SingularSeries
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes

theorem rosser_schoenfeld_totient_bound (H n : ℕ) (hH : 10 ^ 2 ≤ H)
    (hn : n % 2 = 1) (hnH : n ≤ H) :
    (2 * n : ℝ) / Nat.totient (2 * n) ≤
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (2 * (H : ℝ))) +
        2.507 / Real.log (Real.log (2 * (H : ℝ))) := by sorry

end TaoFivePrimes
