-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_pointwise
-- name    : TaoFivePrimes.rosser_schoenfeld_totient_pointwise
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-09-17T08:35:38.323106+00:00
-- url     : https://prove2.me/theorems/f044511a-1bac-4f2f-a2e0-fe2cfec0e5bf
-- title:
--   Rosser–Schoenfeld's pointwise totient bound (Theorem 15)
-- statement:
--   Let $\varphi$ denote Euler's totient function and $\gamma$ the Euler–Mascheroni constant. For every integer $n \ge 3$,
--   $$ \frac{n}{\varphi(n)} \;<\; e^{\gamma}\,\log\log n \;+\; \frac{2.50637}{\log\log n}. $$
--
--   This is Theorem 15 of Rosser and Schoenfeld (1962). The theorem is stated there in two branches: for all $n \ge 3$ one has $\frac{n}{\varphi(n)} < e^{\gamma}\log\log n + \frac{5}{2\log\log n}$ (their equation (3.41)), with the single exceptional integer $n = 223092870 = 2\cdot 3\cdot 5\cdot 7\cdot 11\cdot 13\cdot 17\cdot 19\cdot 23$, for which the sharper bound $\frac{n}{\varphi(n)} < e^{\gamma}\log\log n + \frac{2.50637}{\log\log n}$ holds (their equation (3.42)). Since $5/2 = 2.5 < 2.50637$, the single constant $2.50637$ is valid uniformly for all $n \ge 3$, which is the form stated here.
--
--   The bound is the pointwise input in Tao's proof of Proposition 4.10 (arXiv:1201.6656), where it is applied to $2n$ for odd $n$ and then uniformized in the parameter $H \ge 10^2$.
--
--   Formalization note: `Nat.totient` is Mathlib's totient function, coerced to $\mathbb{R}$; `Real.eulerMascheroniConstant` is $\gamma$; `Real.log (Real.log (n : \mathbb{R}))` is the real logarithm of $\log n$.
-- source:
--   J.B. Rosser, L. Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois Journal of Mathematics 6 (1962), 64–94, https://projecteuclid.org/journals/illinois-journal-of-mathematics/volume-6/issue-1/Approximate-formulas-for-some-functions-of-prime-numbers/10.1215/ijm/1255631807.full, Theorem 15, p. 72, eqs. (3.41)–(3.42); proof in §9, pp. 88–89; used in T. Tao, *Every odd number greater than 1 is the sum of at most five primes*, arXiv:1201.6656, https://arxiv.org/abs/1201.6656, proof of Proposition 4.10.

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes

theorem rosser_schoenfeld_totient_pointwise (n : ℕ) (hn : 3 ≤ n) :
    (n : ℝ) / Nat.totient n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
        2.50637 / Real.log (Real.log (n : ℝ)) := by sorry

end TaoFivePrimes
