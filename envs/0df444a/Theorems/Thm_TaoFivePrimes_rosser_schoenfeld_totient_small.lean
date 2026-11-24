-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_small
-- name    : TaoFivePrimes.rosser_schoenfeld_totient_small
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T08:41:31.647444+00:00
-- url     : https://prove2.me/theorems/da623148-6c5f-4b5b-9b04-1816a95949b2
-- title:
--   Rosser–Schoenfeld's totient bound: finite range $n < e^{294}$
-- statement:
--   Let $\varphi$ be Euler's totient function and $\gamma$ the Euler–Mascheroni constant. For every integer $n$ with $3 \le n < e^{294}$,
--   $$ \frac{n}{\varphi(n)} \;<\; e^{\gamma}\,\log\log n \;+\; \frac{2.50637}{\log\log n}. $$
--
--   This is the finite-range half of Theorem 15 of Rosser and Schoenfeld (1962), whose proof in §9 verifies the estimates numerically for $3 \le n < \exp \theta(313)$ by combining Lemma 14 with the Rosser–Walker prime tabulation: the generic bound $n/\varphi(n) < e^{\gamma}\log\log n + \frac{5}{2\log\log n}$ (equation (3.41)) holds throughout this range with the single exception $n = 223092870 = 2\cdot 3\cdot 5\cdot 7\cdot 11\cdot 13\cdot 17\cdot 19\cdot 23$, where the sharper constant $2.50637$ is needed (equation (3.42)). Since $294 < \theta(313)$ and $5/2 < 2.50637$, the verification yields the displayed uniform statement for all $3 \le n < e^{294}$.
--
--   Together with the analytic range $n \ge e^{294}$ (handled by Lemma 15) this forms the complete proof of Theorem 15.
--
--   Formalization note: `Nat.totient` is Mathlib's totient function coerced to $\mathbb{R}$, `Real.eulerMascheroniConstant` is $\gamma$, and `Real.exp 294` is $e^{294}$.
-- source:
--   J.B. Rosser, L. Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois Journal of Mathematics 6 (1962), 64–94, https://projecteuclid.org/journals/illinois-journal-of-mathematics/volume-6/issue-1/Approximate-formulas-for-some-functions-of-prime-numbers/10.1215/ijm/1255631807.full, Theorem 15, p. 72, eqs. (3.41)–(3.42); finite range: Lemma 14 and §9, pp. 88–89; analytic range: Lemma 15, Theorem 33, §8 eq. (3.29), Theorem 19 and (3.14); used in T. Tao, *Every odd number greater than 1 is the sum of at most five primes*, arXiv:1201.6656, proof of Proposition 4.10.

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes

theorem rosser_schoenfeld_totient_small (n : ℕ) (hn : 3 ≤ n)
    (hfin : (n : ℝ) < Real.exp 294) :
    (n : ℝ) / Nat.totient n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
        2.50637 / Real.log (Real.log (n : ℝ)) := by sorry

end TaoFivePrimes
