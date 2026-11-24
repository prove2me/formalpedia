-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_finite_verification
-- name    : TaoFivePrimes.rosser_schoenfeld_totient_finite_verification
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T08:48:25.872167+00:00
-- url     : https://prove2.me/theorems/a56e196f-89f6-4624-bb60-ade1852c1ed0
-- title:
--   Rosser–Schoenfeld: the finite verification for $3 \le n < e^{294}$
-- statement:
--   For every integer $n$ with $3 \le n < e^{294}$ there exists an integer $m \ge 1$ such that, writing $p_1 < p_2 < \cdots$ for the primes,
--   $$ n < e^{\theta(p_{m+1})} \qquad\text{and}\qquad \prod_{i=1}^{m} \frac{p_i}{p_i - 1} \;<\; e^{\gamma}\,\log\log n + \frac{2.50637}{\log\log n}, $$
--   where $\theta$ is the Chebyshev theta function and $\gamma$ is the Euler–Mascheroni constant.
--
--   This is the numerical verification step in §9 of Rosser and Schoenfeld (1962), pp. 88–89: using values of $\theta(x)$ from the Rosser–Walker prime tabulation, the estimate (3.41) — with constant $5/2$, sharpened to $2.50637$ in the exceptional case $n = 223092870 = 2\cdot 3\cdot 5\cdot 7\cdot 11\cdot 13\cdot 17\cdot 19\cdot 23$ (equation (3.42)) — is checked step by step for $3 \le n < e^{\theta(313)}$. For $n$ in the interval $[e^{\theta(p_m)}, e^{\theta(p_{m+1})})$ the inequality is checked at the left endpoint and transported to $n$ by monotonicity of $\log\log$. Since $294 < \theta(313)$ and $5/2 < 2.50637$, this covers all $3 \le n < e^{294}$ with the uniform constant $2.50637$. Combined with Lemma 14 (which converts the primorial bound into a bound for $n/\varphi(n)$) this gives the finite half of Theorem 15.
--
--   Formalization note: `Chebyshev.theta` is Mathlib's $\theta$, `Nat.nth Nat.Prime m` is $p_{m+1}$ (zero-indexed), and `Real.exp 294` is $e^{294}$.
-- source:
--   J.B. Rosser, L. Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois Journal of Mathematics 6 (1962), 64–94, https://projecteuclid.org/journals/illinois-journal-of-mathematics/volume-6/issue-1/Approximate-formulas-for-some-functions-of-prime-numbers/10.1215/ijm/1255631807.full, §9, Lemma 14, p. 88, and pp. 88–89 for the Rosser–Walker verification; used in T. Tao, *Every odd number greater than 1 is the sum of at most five primes*, arXiv:1201.6656, proof of Proposition 4.10.

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Nth
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

namespace TaoFivePrimes

theorem rosser_schoenfeld_totient_finite_verification (n : ℕ) (hn : 3 ≤ n)
    (hfin : (n : ℝ) < Real.exp 294) :
    ∃ m : ℕ, 1 ≤ m ∧ (n : ℝ) < Real.exp (Chebyshev.theta (Nat.nth Nat.Prime m)) ∧
      (∏ i ∈ Finset.range m,
        (Nat.nth Nat.Prime i : ℝ) / ((Nat.nth Nat.Prime i : ℝ) - 1)) <
        Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
          2.50637 / Real.log (Real.log (n : ℝ)) := by sorry

end TaoFivePrimes
