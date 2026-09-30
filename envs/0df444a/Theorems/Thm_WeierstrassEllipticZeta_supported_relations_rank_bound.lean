-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_supported_relations_rank_bound
-- name    : WeierstrassEllipticZeta.supported_relations_rank_bound
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-13T03:23:23.398107+00:00
-- url     : https://prove2.me/theorems/dd877c9f-3942-49b3-92c0-642e9ba583a2
-- title:
--   Supported polynomial relations bound the dimension of a monomial image span
-- statement:
--   Let $K$ be a field, $V$ a $K$-vector space, and $E:K[\sigma]\to V$ a $K$-linear map. For a finite exponent set $S\subseteq\mathbb N^{(\sigma)}$, let $A_S$ be the space of polynomials supported in $S$. Let $R$ be a linear subspace of $A_S$ such that $E(p)=0$ for every $p\in R$. Then
--   $$
--   \dim_K\operatorname{span}_K\{E(X^d):d\in S\}+\dim_K R\le |S|.
--   $$
--   The space $R$ may be any subspace of relations; it need not contain all supported polynomials annihilated by $E$. No finite-dimensionality of the ambient vector space is assumed, and empty exponent sets are allowed.
-- source:
--   Derived relation-space certificate for the frontier https://prove2.me/theorems/2d6c7d2d-cec1-45b0-82c6-8c316add1adb. The mission setting is Senthil Kumar K (2026), Algebraic independence of values of Weierstrass elliptic and zeta functions, Appendix A.2 and Theorem A.2, https://doi.org/10.1017/S001309152610145X. The supporting bound uses the monomial basis of a restricted-support polynomial space and rank-nullity in Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. The uniform geometric relation bound remains open.

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Span.Basic

noncomputable section

theorem WeierstrassEllipticZeta.supported_relations_rank_bound
    (K σ V : Type*) [Field K] [AddCommGroup V] [Module K V]
    (E : MvPolynomial σ K →ₗ[K] V) (S : Finset (σ →₀ ℕ))
    (R : Submodule K (MvPolynomial.restrictSupport K (S : Set (σ →₀ ℕ))))
    (hR : ∀ p : R, E p.val.val = 0) :
    Module.finrank K (Submodule.span K
      ((fun d : σ →₀ ℕ => E (MvPolynomial.monomial d 1)) '' (S : Set (σ →₀ ℕ)))) +
      Module.finrank K R ≤ S.card := by sorry
