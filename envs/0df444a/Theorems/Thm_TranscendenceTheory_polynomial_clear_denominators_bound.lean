-- Prove2me | Theorems.Thm_TranscendenceTheory_polynomial_clear_denominators_bound
-- name    : TranscendenceTheory.polynomial_clear_denominators_bound
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-07T11:57:32.149783+00:00
-- url     : https://prove2.me/theorems/79e55993-e3ca-41ad-b8d7-2e6976dc1b6d
-- title:
--   Clearing coordinate denominators with degree and coefficient bounds
-- statement:
--   Let $I$ be a finite set, let $J$ be any set of variables, and let $A$ be a commutative ring. For an integer polynomial, write
--
--   $$
--   \ell(P)=\sum_m |[X^m]P|.
--   $$
--
--   Let $P\in\mathbb Z[X_i:i\in I]$ satisfy $\deg_{X_i}P\le k_i$. For each $i$, let $S_i,Q_i\in\mathbb Z[T_j:j\in J]$ have total degree at most $d_i$ and coefficient length at most $H_i$, where $k_i,d_i,H_i$ are nonnegative integers.
--
--   There exists an integer polynomial $R$ such that
--
--   $$
--   \deg R\le\sum_i k_i d_i,
--   \qquad \ell(R)\le\ell(P)\prod_i H_i^{k_i},
--   $$
--
--   and, for every ring homomorphism $\phi:\mathbb Z[T_j]\to A$ and every tuple $y\in A^I$ satisfying $\phi(S_i)=\phi(Q_i)y_i$,
--
--   $$
--   \phi(R)=\left(\prod_i\phi(Q_i)^{k_i}\right)P(y).
--   $$
--
--   The polynomial $R$ is chosen before the homomorphism and the evaluation tuple. Thus the same polynomial works under every compatible evaluation. No denominator is inverted, so zero denominators and rings with zero divisors are allowed. Empty variable sets and zero exponents are included, using $0^0=1$ and total degree zero for the zero polynomial. Separate coordinate bounds preserve the distinct arithmetic costs of the fixed and moving elliptic values.
-- source:
--   Coordinatewise polynomial homogenization underlying Senthil Kumar K (2026), Section 5 Lemma 7(b), especially equations (20)-(27), and the substitution estimates of Lemma 1(iii). This quantitative algebraic formulation is not a verbatim theorem in the source. https://doi.org/10.1017/S001309152610145X

import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic.Ring

open MvPolynomial

theorem TranscendenceTheory.polynomial_clear_denominators_bound {σ τ A : Type} [Fintype σ] [CommRing A]
    (p : MvPolynomial σ ℤ) (k d H : σ → ℕ)
    (s q : σ → MvPolynomial τ ℤ)
    (hp : ∀ i, p.degreeOf i ≤ k i)
    (hs_degree : ∀ i, (s i).totalDegree ≤ d i)
    (hq_degree : ∀ i, (q i).totalDegree ≤ d i)
    (hs_length : ∀ i, (∑ m ∈ (s i).support, ((s i).coeff m).natAbs) ≤ H i)
    (hq_length : ∀ i, (∑ m ∈ (q i).support, ((q i).coeff m).natAbs) ≤ H i) :
    ∃ r : MvPolynomial τ ℤ,
      r.totalDegree ≤ ∑ i, k i * d i ∧
      (∑ m ∈ r.support, (r.coeff m).natAbs) ≤
        (∑ m ∈ p.support, (p.coeff m).natAbs) * ∏ i, H i ^ k i ∧
      ∀ (φ : MvPolynomial τ ℤ →+* A) (y : σ → A),
        (∀ i, φ (s i) = φ (q i) * y i) →
        φ r = (∏ i, φ (q i) ^ k i) * eval₂ (Int.castRingHom A) y p := by sorry
