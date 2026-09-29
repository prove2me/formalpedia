-- Prove2me | Theorems.Thm_PrimePairSieve_polynomial_sieve_bound
-- name    : PrimePairSieve.polynomial_sieve_bound
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-19T22:34:32.384049+00:00
-- url     : https://prove2.me/theorems/db9f09de-4c5c-443d-bebf-40b37f758d32
-- title:
--   A concrete Selberg sieve inequality for the prime-pair polynomial
-- statement:
--   Let $d$ be a positive even natural number, $P$ a squarefree natural number, and $N$ a natural interval length. Let $w$ be arbitrary real weights satisfying $w(1)=1$. Define the actual root count and the squared sieve coefficients by
--
--   $$\rho_d(m)=\#\{0\le r<m:m\mid r(r+d)\},\qquad
--   \Lambda^2w(m)=\sum_{\substack{a\mid m,\ b\mid m\\\operatorname{lcm}(a,b)=m}}w(a)w(b).$$
--
--   Then
--
--   $$\#\{0\le n<N:\gcd(P,n(n+d))=1\}
--   \le N\sum_{m\mid P}\Lambda^2w(m)\frac{\rho_d(m)}m
--   +\sum_{m\mid P}|\Lambda^2w(m)|\rho_d(m).$$
--
--   The only assumptions are the displayed conditions on $N,d,P,w$. In particular, no distribution estimate is an input hypothesis.
--
--   This is an arithmetic input to a prime-pair sieve, with the weight choice and denominator estimates left explicit. It does not prove the final sharp Siebert bound: small primes removed by the sieve and the numerical constant require further work.
-- source:
--   Classical Selberg upper-bound sieve, using Mathlib/NumberTheory/SelbergSieve.lean (Arend Mellendijk,2024), revision0df444a360eaa60ab8c11dca51a86af692955474. The concrete polynomial root counts and interval remainder are proved in this development. Intended consumer: T. Tao, Every odd number greater than1 is the sum of at most five primes, Proposition4.10, https://arxiv.org/abs/1201.6656 ; exact Prove2Me target https://prove2.me/theorems/0b3aa912-642f-4b13-b915-0b43c7e7c385 . Known arithmetic sieve infrastructure; no novelty claim.

import Mathlib.NumberTheory.SelbergSieve
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve.polynomial_sieve_bound
    (N d P : ℕ) (hd0 : 0 < d) (hd2 : 2 ∣ d) (hP : Squarefree P)
    (w : ℕ → ℝ) (hw : w 1 = 1) :
    (((Finset.range N).filter (fun n => P.Coprime (n * (n + d)))).card : ℝ) ≤
      (N : ℝ) * (∑ m ∈ P.divisors, BoundingSieve.lambdaSquared w m *
        (((Finset.range m).filter (fun r => m ∣ r * (r + d))).card : ℝ) / (m : ℝ)) +
        ∑ m ∈ P.divisors, |BoundingSieve.lambdaSquared w m| *
          (((Finset.range m).filter (fun r => m ∣ r * (r + d))).card : ℝ) := by sorry
