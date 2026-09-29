-- Prove2me | Theorems.Thm_SelbergOptimization_supported_weights
-- name    : SelbergOptimization.supported_weights
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-19T22:31:15.517719+00:00
-- url     : https://prove2.me/theorems/83c982b2-4109-4642-bd76-e82a6ac1341b
-- title:
--   Supported Selberg weights attaining the reciprocal denominator
-- statement:
--   Let $A$ be a finite set of natural numbers with nonnegative real weights $a_n$, let $P$ be a squarefree positive integer, and let $X$ be a real mass parameter. Let $\nu$ be a multiplicative arithmetic function with $0<\nu(p)<1$ for every prime $p\mid P$. Set
--
--   $$A_m=\sum_{\substack{n\in A\\m\mid n}}a_n,\qquad R_m=A_m-X\nu(m),\qquad
--   S=\sum_{\substack{n\in A\\\gcd(n,P)=1}}a_n.$$
--
--   For $z\ge1$, define
--
--   $$g(m)=\nu(m)\prod_{p\mid m}(1-\nu(p))^{-1},\qquad G(z)=\sum_{\substack{m\mid P\\m\le z}}g(m).$$
--
--   There are real weights $w$ satisfying $w(1)=1$ and $w(m)=0$ for $m>z$ such that, writing $\Lambda^2w(m)=\sum_{a\mid m,\ b\mid m,\ \operatorname{lcm}(a,b)=m}w(a)w(b)$, one has
--
--   $$\sum_{m\mid P}\Lambda^2w(m)\nu(m)=\frac1{G(z)},\qquad
--   S\le\frac{X}{G(z)}+\sum_{m\mid P}|\Lambda^2w(m)|\,|R_m|.$$
--
--   The same weights supply the normalization, finite cutoff, exact main term and sifted bound. This construction provides the weight-selection step of an upper-bound sieve; a numerical remainder estimate is a separate requirement. No variational minimality is asserted.
--
--   **Formalization Note** The sieve data, main sum and absolute remainder sum are Mathlib's `BoundingSieve`, `mainSum` and `errSum`. All sums above are finite.
-- source:
--   Classical Selberg upper-bound sieve, formal continuation of Mathlib/NumberTheory/SelbergSieve.lean (Arend Mellendijk, 2024), revision0df444a360eaa60ab8c11dca51a86af692955474, especially mainSum_lambdaSquared_eq_sum_mul_sum_sq. The explicit weights here are constructed by divisor Möbius inversion. https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/SelbergSieve.lean . Intended consumer: TaoFivePrimes.siebert_prime_pair_bound, https://prove2.me/theorems/0b3aa912-642f-4b13-b915-0b43c7e7c385 . Known mathematics; no novelty claim.

import Mathlib.NumberTheory.SelbergSieve
open scoped BigOperators
set_option autoImplicit false

theorem SelbergOptimization.supported_weights (s : BoundingSieve) (z : ℝ) (hz : 1 ≤ z) :
    ∃ w : ℕ → ℝ, w 1 = 1 ∧ (∀ d : ℕ, z < (d : ℝ) → w d = 0) ∧
      s.mainSum (BoundingSieve.lambdaSquared w) =
        (∑ e ∈ s.prodPrimes.divisors, if (e : ℝ) ≤ z then s.selbergTerms e else 0)⁻¹ ∧
      s.siftedSum ≤ s.totalMass /
        (∑ e ∈ s.prodPrimes.divisors, if (e : ℝ) ≤ z then s.selbergTerms e else 0) +
        s.errSum (BoundingSieve.lambdaSquared w) := by sorry
