-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_large
-- name    : TaoFivePrimes.rosser_schoenfeld_totient_large
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-09-17T08:41:31.220793+00:00
-- url     : https://prove2.me/theorems/d8c0e8fa-2390-4abb-bb18-e985968c227b
-- title:
--   Rosser–Schoenfeld's totient bound: analytic range $e^{294} \le n$
-- statement:
--   Let $\varphi$ be Euler's totient function and $\gamma$ the Euler–Mascheroni constant. For every integer $n \ge e^{294}$,
--   $$ \frac{n}{\varphi(n)} \;<\; e^{\gamma}\,\log\log n \;+\; \frac{2.50637}{\log\log n}. $$
--
--   This is the analytic-range half of Theorem 15 of Rosser and Schoenfeld (1962). In §9, for $\log n \ge 294$ (the argument in fact applies from $\log n > 255$), Lemma 15 combines Theorem 33 with the explicit Mertens product estimate (3.29) of §8 and the Chebyshev bounds for $\theta$ (Theorem 19, inequality (3.14)) to establish $n/\varphi(n) < e^{\gamma}\log\log n + \frac{5}{2\log\log n}$. Since $5/2 < 2.50637$, this yields the displayed uniform constant. Together with the finite range $3 \le n < e^{294}$ (handled by Lemma 14 and numerical verification) this forms the complete proof of Theorem 15.
--
--   Formalization note: `Nat.totient` is Mathlib's totient function coerced to $\mathbb{R}$, `Real.eulerMascheroniConstant` is $\gamma$, and $e^{294}$ enters the hypothesis as `Real.exp 294 \u2264 (n : \u211d)`.
-- source:
--   J.B. Rosser, L. Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois Journal of Mathematics 6 (1962), 64–94, https://projecteuclid.org/journals/illinois-journal-of-mathematics/volume-6/issue-1/Approximate-formulas-for-some-functions-of-prime-numbers/10.1215/ijm/1255631807.full, Theorem 15, p. 72, eqs. (3.41)–(3.42); finite range: Lemma 14 and §9, pp. 88–89; analytic range: Lemma 15, Theorem 33, §8 eq. (3.29), Theorem 19 and (3.14); used in T. Tao, *Every odd number greater than 1 is the sum of at most five primes*, arXiv:1201.6656, proof of Proposition 4.10.

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes

theorem rosser_schoenfeld_totient_large (n : ℕ) (hn : 3 ≤ n)
    (hlarge : Real.exp 294 ≤ (n : ℝ)) :
    (n : ℝ) / Nat.totient n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
        2.50637 / Real.log (Real.log (n : ℝ)) := by sorry

end TaoFivePrimes
