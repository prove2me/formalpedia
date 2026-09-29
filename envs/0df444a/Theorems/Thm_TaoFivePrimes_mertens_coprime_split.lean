-- Prove2me | Theorems.Thm_TaoFivePrimes_mertens_coprime_split
-- name    : TaoFivePrimes.mertens_coprime_split
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T01:54:35.563087+00:00
-- url     : https://prove2.me/theorems/92411c20-8740-4857-bf3d-f23b3045fbd0
-- title:
--   Tao Lemma 4.6 (proof): removing the small primes from the Montgomery-Vaughan sum
-- statement:
--   For all integers $Q,R\ge 0$,
--
--   $$\sum_{q\le R}\frac{\mu^2(q)}{\varphi(q)}\;\le\;\left(\sum_{\substack{q\le R\\ (q,Q\sharp)=1}}\frac{\mu^2(q)}{\varphi(q)}\right)\prod_{p\le Q}\frac{p}{p-1},$$
--
--   where $\mu$ is the Möbius function, $\varphi$ is Euler's totient, $Q\sharp=\prod_{p\le Q}p$ is the primorial, and both the sum and the product on the right run over the integers, respectively the primes, in $[1,Q]$ and $[1,R]$.
--
--   In words: restricting the Montgomery–Vaughan sum $G(R)=\sum_{q\le R}\mu^2(q)/\varphi(q)$ to moduli free of small prime factors costs at most the Mertens product $\prod_{p\le Q}p/(p-1)$. It is the step that converts the unrestricted lower bound $G(R)\ge\log R$ into the lower bound for the restricted sum which weights the Farey translates in the local $L^2$ estimate for smoothed prime exponential sums; combined with $G(R)\ge\log R$ it gives
--
--   $$\sum_{\substack{q\le R\\ (q,Q\sharp)=1}}\frac{\mu^2(q)}{\varphi(q)}\;\ge\;\frac{\log R}{\prod_{p\le Q}p/(p-1)} .$$
--
--   The mechanism is the factorization of a squarefree modulus into its $Q$-smooth and $Q$-rough parts, together with the multiplicativity of $\mu^2/\varphi$; the Euler product $\prod_{p\le Q}(1+\frac{1}{p-1})$ collects the smooth parts.
--
--   **Formalization Note** The Möbius function is the arithmetic function $\mu$ of the ambient library, cast to the reals, and the coprimality condition is written as coprimality to the product of the primes in $[1,Q]$ rather than as a condition on each small prime. For $q=0$ the summand is $0/0=0$ under the ambient division convention, and the sum starts at $q=1$ in any case.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 4, proof of Lemma 4.6 (Local L^2 estimate), the display 'Observe that G(R) <= (sum_{q_1 <= R, (q_1, Q#)=1} mu^2(q_1)/phi(q_1)) (prod_{p <= Q} 1 + 1/phi(p))'

import Mathlib

open Finset

theorem TaoFivePrimes.mertens_coprime_split (Q R : ℕ) :
    (∑ n ∈ Finset.Icc 1 R,
        ((ArithmeticFunction.moebius n : ℝ)) ^ 2 / (Nat.totient n : ℝ))
      ≤ (∑ m ∈ (Finset.Icc 1 R).filter
            (fun m => Nat.Coprime m (∏ p ∈ (Finset.Icc 1 Q).filter Nat.Prime, p)),
          ((ArithmeticFunction.moebius m : ℝ)) ^ 2 / (Nat.totient m : ℝ))
        * ∏ p ∈ (Finset.Icc 1 Q).filter Nat.Prime, ((p : ℝ) / ((p : ℝ) - 1)) := by sorry
