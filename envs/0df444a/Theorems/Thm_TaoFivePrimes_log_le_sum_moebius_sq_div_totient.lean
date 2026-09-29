-- Prove2me | Theorems.Thm_TaoFivePrimes_log_le_sum_moebius_sq_div_totient
-- name    : TaoFivePrimes.log_le_sum_moebius_sq_div_totient
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-09-14T01:05:59.804903+00:00
-- url     : https://prove2.me/theorems/0bcddaab-96d9-40ff-a8e8-46ddd6e4d607
-- title:
--   Montgomery-Vaughan: sum_{q <= R} mu^2(q)/phi(q) >= log R
-- statement:
--   For a real number $R \ge 0$ put
--
--   $$G(R)\;:=\;\sum_{q\le R}\frac{\mu^{2}(q)}{\varphi(q)},$$
--
--   the sum being over the positive integers $q$ at most $R$, with $\mu$ the Möbius function and $\varphi$ Euler's totient. Then
--
--   $$G(R)\;\ge\;\log R .$$
--
--   Only the squarefree $q$ contribute, and for those $\mu^{2}(q)=1$, so $G(R)=\sum_{q\le R,\ q\ \text{squarefree}}1/\varphi(q)$.
--
--   This is the elementary half of the estimate of van Lint and Richert, sharpened by Montgomery and Vaughan to $G(R)\ge\log R+1.07$ for $R\ge6$. It is the input that converts the averaging over moduli in the local $L^{2}$ estimate (Tao's Lemma 4.6) into the saving of $\log x/\log R$ over the global $L^{2}$ estimate of Lemma 4.5, and hence it underlies Corollary 4.7, the upper bound on the major-arc $L^{2}$ mass. The bound is sharp in order: $G(R)\sim\log R$ as $R\to\infty$.
--
--   **Formalization Note** The sum ranges over the integers from $1$ to $\lfloor R\rfloor$, and $\mu$ takes integer values whose square is cast to a real number. No lower bound on $R$ is needed: for $R<1$ the logarithm is negative while the sum is non-negative, and for $R=0$ the convention $\log 0=0$ still leaves the inequality true with an empty sum.
-- source:
--   Terence Tao, "Every odd number greater than 1 is the sum of at most five primes", Mathematics of Computation 83 (2014), 997-1038; arXiv:1201.6656, https://arxiv.org/abs/1201.6656, Section 4, the estimate G(R) >= log R quoted in the proof of Lemma 4.6 (Local L^2 estimate); originally J. E. van Lint and H. E. Richert, On primes in arithmetic progressions, Acta Arith. 11 (1965), 209-216, and H. L. Montgomery and R. C. Vaughan, The large sieve, Mathematika 20 (1973), 119-134, Lemma 3

import Mathlib

open Finset

theorem TaoFivePrimes.log_le_sum_moebius_sq_div_totient (R : ℝ) (hR : 0 ≤ R) :
    Real.log R ≤ ∑ q ∈ Finset.Icc 1 ⌊R⌋₊,
      ((ArithmeticFunction.moebius q : ℝ) ^ 2 / (Nat.totient q : ℝ)) := by sorry
