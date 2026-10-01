-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_lemma15_small_range
-- name    : TaoFivePrimes.rosser_schoenfeld_totient_lemma15_small_range
-- status  : Proved
-- author  : @chstdu
-- created : 2026-09-22T08:10:27.597241+00:00
-- url     : https://prove2.me/theorems/4fe39f0c-40f9-4dac-9eac-7fbe16dfd3c9
-- statement:
--   Let $n > 1$ be an integer, $y$ a real number, $\varphi$ Euler's totient function, $\gamma$ the Euler–Mascheroni constant, and $\theta$ the Chebyshev theta function. Assume
--   $$ 2.88 \le \log n + y, \qquad \log n < \theta(\log n + y), \qquad 0 \le y - 2 \le \frac{0.9\,\log n}{\log\log n}, \qquad \log n + y - 2 < 286. $$
--   Then
--   $$ \frac{n}{\varphi(n)} \;<\; e^{\gamma}\,\log\log n + \frac{5}{2\log\log n}. $$
--
--   This is the small-range companion of Lemma 15 of Rosser and Schoenfeld (1962), §9 (p. 88): the restriction of the platform theorem `TaoFivePrimes.rosser_schoenfeld_totient_lemma15` to the range $\log n + y - 2 < 286$, i.e. the finite part of inequality (3.41) below the analytic threshold $x = 286$ of the Mertens-type product bound (3.29). In this range the product route of Theorem 33 followed by (3.29) is not available ((3.29) is only valid for $x \ge 286$), but the inequality remains true: for $\log n + y < 5$ only finitely many $n \le 20$ occur, and in the intermediate range $5 \le \log n + y - 2 < 286$ the extremal values of $n/\varphi(n)$ are attained at primorials $p_k^\#$, and the hypothesis $\log n < \theta(\log n + y)$ together with the cap $y - 2 \le 0.9 \log n / \log\log n$ excludes exactly those near-primorial configurations for which the primorial product $\prod_{p \le p_k} p/(p-1)$ would exceed $e^{\gamma} \log\log n + 5/(2\log\log n)$; for example $n = 23^\#$ is excluded because reaching the next prime $29$ would require $y \ge 29 - \log(23^\#) \approx 9.78$, violating the cap $y \le 2 + 0.9\log(23^\#)/\log\log(23^\#) \approx 7.85$.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), 64-94, Section 9, Lemma 15 (p. 88), https://projecteuclid.org/journals/illinois-journal-of-mathematics/volume-6/issue-1/Approximate-Formulas-for-Some-Functions-of-Prime-Numbers/ijm/1255627471.full (finite-range restriction of Prove2Me theorem TaoFivePrimes.rosser_schoenfeld_totient_lemma15)

import Mathlib

namespace TaoFivePrimes

theorem rosser_schoenfeld_totient_lemma15_small_range (n : ℕ) (y : ℝ) (hn : 1 < n)
    (h1 : 2.88 ≤ Real.log (n : ℝ) + y)
    (h2 : Real.log (n : ℝ) < Chebyshev.theta (Real.log (n : ℝ) + y))
    (h3 : 0 ≤ y - 2)
    (h4 : y - 2 ≤ 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))
    (h5 : Real.log (n : ℝ) + y - 2 < 286) :
    (n : ℝ) / Nat.totient n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
        5 / (2 * Real.log (Real.log (n : ℝ))) := by sorry

end TaoFivePrimes
