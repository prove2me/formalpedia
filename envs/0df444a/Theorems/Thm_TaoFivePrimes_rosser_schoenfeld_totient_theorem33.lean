-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_theorem33
-- name    : TaoFivePrimes.rosser_schoenfeld_totient_theorem33
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T09:14:17.743396+00:00
-- url     : https://prove2.me/theorems/2eee1f8e-b44a-47fb-a6d7-211c59332573
-- title:
--   Rosser–Schoenfeld (1962), Theorem 33: totient bound via primorial
-- statement:
--   **Rosser--Schoenfeld (1962), Theorem 33.** Let $x \ge 5$ be a real number and $n \ge 1$ an integer with
--   $$n < e^{\theta(x)},$$
--   where $\theta(x) = \sum_{p \le x} \log p$ is the first Chebyshev function (the sum over primes $p \le x$). Then
--   $$\frac{n}{\varphi(n)} \;\le\; \prod_{p \le x-2} \frac{p}{p-1},$$
--   where $\varphi$ is Euler's totient function and the product is over all primes $p \le \lfloor x-2 \rfloor$.
--
--   This is the comparison theorem that transfers information about Chebyshev's $\theta$ function into a bound for the primorial-type product $\prod_{p \le x-2} p/(p-1)$, which dominates $n/\varphi(n)$ whenever $n < e^{\theta(x)}$. It is Theorem 33 in §9 of the source, used in the proof of Lemma 15.
-- source:
--   J.B. Rosser, L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64–94; §9, pp. 88–89, Theorem 33. https://doi.org/10.1215/ijm/1255631807

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting

namespace TaoFivePrimes
theorem rosser_schoenfeld_totient_theorem33 (x : ℝ) (n : ℕ) (hx : 5 ≤ x) (hn : 1 ≤ n)
    (h : (n : ℝ) < Real.exp (Chebyshev.theta x)) :
    (n : ℝ) / Nat.totient n ≤
      ∏ p ∈ Nat.primesLE ⌊x - 2⌋₊, (p : ℝ) / ((p : ℝ) - 1) := by sorry
end TaoFivePrimes
