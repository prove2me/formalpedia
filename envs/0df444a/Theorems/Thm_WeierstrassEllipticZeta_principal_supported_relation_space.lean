-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_principal_supported_relation_space
-- name    : WeierstrassEllipticZeta.principal_supported_relation_space
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-13T03:37:29.298736+00:00
-- url     : https://prove2.me/theorems/d90465d3-47a7-4f78-a666-2d46a0c38303
-- title:
--   Supported relation spaces from monomial multiples of a nonzero polynomial
-- statement:
--   Let $K$ be a field, $p\in K[\sigma]$ a nonzero polynomial, and $S,T\subseteq\mathbb N^{(\sigma)}$ finite exponent sets. Assume that
--   $$\operatorname{supp}(pX^d)\subseteq S\qquad\text{for every }d\in T.$$
--   Let $A_S$ be the vector space of polynomials supported in $S$. There exists a linear subspace $R\subseteq A_S$ with
--   $$\dim_K R=|T|$$
--   such that, for every ideal $I\subseteq K[\sigma]$ containing $p$, every polynomial in $R$ belongs to $I$.
--
--   The same space $R$ works for all ideals containing $p$. The exponent sets may be empty; neither an ordering of the monomials nor a Gröbner basis is assumed.
-- source:
--   Derived construction of supported relation spaces for the frontier https://prove2.me/theorems/2053281f-559d-4942-9256-658282218fcc. The mission setting is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The supporting construction uses injectivity of multiplication by a nonzero polynomial, finite monomial bases, and closure of ideals under multiplication in Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. The uniform geometric support and cardinality construction remains open.

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Span.Basic

noncomputable section

theorem WeierstrassEllipticZeta.principal_supported_relation_space
    (K σ : Type*) [Field K] (p : MvPolynomial σ K) (hp : p ≠ 0)
    (S T : Finset (σ →₀ ℕ))
    (hsupport : ∀ d ∈ T, (p * MvPolynomial.monomial d 1).support ⊆ S) :
    ∃ R : Submodule K (MvPolynomial.restrictSupport K (S : Set (σ →₀ ℕ))),
      Module.finrank K R = T.card ∧
      ∀ I : Ideal (MvPolynomial σ K), p ∈ I → ∀ q : R, q.val.val ∈ I := by sorry
