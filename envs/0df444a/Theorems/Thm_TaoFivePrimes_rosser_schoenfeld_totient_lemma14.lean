-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_lemma14
-- name    : TaoFivePrimes.rosser_schoenfeld_totient_lemma14
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T08:48:24.939804+00:00
-- url     : https://prove2.me/theorems/6c9abb37-1748-4613-8f15-5384cdaf3cd0
-- title:
--   Rosser–Schoenfeld's Lemma 14: the primorial bound for $n/\varphi(n)$
-- statement:
--   Let $n, m$ be positive integers, let $p_1 < p_2 < \cdots$ be the primes, let $\varphi$ be Euler's totient function, and let $\theta$ be the Chebyshev theta function. If
--   $$ n < e^{\theta(p_{m+1})}, $$
--   then
--   $$ \frac{n}{\varphi(n)} \;\le\; \prod_{i=1}^{m} \frac{p_i}{p_i - 1}. \qquad (9.1) $$
--
--   This is Lemma 14 of Rosser and Schoenfeld (1962), §9, p. 88, the elementary primorial bound underlying Theorem 15. Proof (as in the source): if $q_1 < \cdots < q_r$ are the distinct primes dividing $n$, then $p_1\cdots p_r \le q_1\cdots q_r \le n < p_1\cdots p_{m+1}$, so $r \le m$; moreover $q_i \ge p_i$ and the map $t \mapsto t/(t-1)$ is decreasing for $t \ge 2$, so $\prod_{i=1}^{r} \frac{q_i}{q_i-1} \le \prod_{i=1}^{r}\frac{p_i}{p_i-1} \le \prod_{i=1}^{m}\frac{p_i}{p_i-1}$. Since $n/\varphi(n) = \prod_{q \mid n} \frac{q}{q-1}$, the claim follows.
--
--   Formalization note: `Chebyshev.theta` is Mathlib's $\theta$, and `Nat.nth Nat.Prime m` is the $(m+1)$-st prime (zero-indexed), i.e. $p_{m+1}$.
-- source:
--   J.B. Rosser, L. Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois Journal of Mathematics 6 (1962), 64–94, https://projecteuclid.org/journals/illinois-journal-of-mathematics/volume-6/issue-1/Approximate-formulas-for-some-functions-of-prime-numbers/10.1215/ijm/1255631807.full, §9, Lemma 14, p. 88, and pp. 88–89 for the Rosser–Walker verification; used in T. Tao, *Every odd number greater than 1 is the sum of at most five primes*, arXiv:1201.6656, proof of Proposition 4.10.

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Nth
import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes

theorem rosser_schoenfeld_totient_lemma14 (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (h : (n : ℝ) < Real.exp (Chebyshev.theta (Nat.nth Nat.Prime m))) :
    (n : ℝ) / Nat.totient n ≤
      ∏ i ∈ Finset.range m,
        (Nat.nth Nat.Prime i : ℝ) / ((Nat.nth Nat.Prime i : ℝ) - 1) := by sorry

end TaoFivePrimes
