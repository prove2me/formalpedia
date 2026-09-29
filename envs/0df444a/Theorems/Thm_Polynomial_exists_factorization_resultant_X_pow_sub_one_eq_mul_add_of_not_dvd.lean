-- Prove2me | Theorems.Thm_Polynomial_exists_factorization_resultant_X_pow_sub_one_eq_mul_add_of_not_dvd
-- name    : Polynomial.exists_factorization_resultant_X_pow_sub_one_eq_mul_add_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/405f0b2e-38fb-535c-a922-c20104eb6a3f
-- title:
--   Lifting the exponent for Res(Xⁿ-1,P) along ℓ-power multiples
-- statement:
--   Let $P \in \mathbb{Z}[X]$ be monic, let $\ell$ be a prime, assume $\ell$ does not divide the constant coefficient $P(0) =$ `P.coeff 0`, and assume that the resultant $\operatorname{Res}(X^n - 1, P)$ is nonzero for every integer $n > 0$ (equivalently, no root of $P$ is a root of unity). Then there exist an integer $m_0 > 0$ and a natural number $c$ such that for every $j > 0$ with $\ell \nmid j$ and every $k \geq 0$, the exponent of $\ell$ in the prime factorisation of the natural number $\lvert \operatorname{Res}(X^{m_0 j \ell^k} - 1, P) \rvert$ equals $(\deg P)\, k + c$, where $\deg P$ is the `natDegree` of $P$. Thus along the multiples of $m_0$ of the shape $m_0 j \ell^k$ the $\ell$-adic valuation of the resultant is an affine function of $k = v_\ell(m_0 j \ell^k)/v_\ell$-part alone, with slope exactly $\deg P$, and a single constant $c$ serves all $j$ prime to $\ell$ simultaneously (a sharpening of the version in which $c$ may depend on the multiple $m_0 j$).
--
--   This is a lifting-the-exponent statement for the quantities $\operatorname{Res}(X^n - 1, P) = \pm\prod_i(\omega_i^n - 1)$, $\omega_i$ the roots of $P$; taking $P$ to be the characteristic polynomial of a Frobenius endomorphism, these resultants are the class numbers (orders of the degree-zero Picard groups) in the tower of constant field extensions of a curve over a finite field. It is used in the computation of those orders, via [`AlgebraicCurve.Pic0.abelJacobiCard_genusFF_of_frobenius_of_isAlgebraic`](thm.html#AlgebraicCurve.Pic0.abelJacobiCard_genusFF_of_frobenius_of_isAlgebraic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_exists_factorization_resultant_X_pow_sub_one_eq_mul_add_of_not_dvd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Polynomial.exists_factorization_resultant_X_pow_sub_one_eq_mul_add_of_not_dvd
    (P : Polynomial ℤ) (hP : P.Monic) (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ¬ ((ℓ : ℤ) ∣ P.coeff 0))
    (hres : ∀ n : ℕ, 0 < n → (Polynomial.X ^ n - 1 : Polynomial ℤ).resultant P ≠ 0) :
    ∃ m₀ : ℕ, 0 < m₀ ∧ ∃ c : ℕ, ∀ j : ℕ, 0 < j → ¬ ℓ ∣ j → ∀ k : ℕ,
        ((Polynomial.X ^ (m₀ * j * ℓ ^ k) - 1 : Polynomial ℤ).resultant P).natAbs.factorization ℓ =
          P.natDegree * k + c := by sorry
