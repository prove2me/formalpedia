-- Prove2me | Theorems.Thm_Submodule_span_fixedPoints_semilinear_eq_top
-- name    : Submodule.span_fixedPoints_semilinear_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/59a50eca-6f3a-58f7-8de2-9ed969f9cb1f
-- title:
--   Fixed vectors of a semilinear Galois action span
-- statement:
--   Let $K$ and $L$ be fields with $L$ a finite-dimensional Galois extension of $K$, and let $V$ be an additive group carrying compatible module structures over $L$ and over $K$ forming a scalar tower over $K \subseteq L$. Let $\rho$ assign to each $\sigma$ in the group $L \simeq_{\text{alg}[K]} L$ of $K$-algebra automorphisms of $L$ an additive endomorphism $\rho(\sigma)$ of $V$, subject to three hypotheses: semilinearity, $\rho(\sigma)(a \cdot v) = \sigma(a) \cdot \rho(\sigma)(v)$ for all $\sigma$, all $a \in L$ and all $v \in V$; unitality, $\rho(1)(v) = v$ for all $v$; and multiplicativity, $\rho(\sigma\tau)(v) = \rho(\sigma)(\rho(\tau)(v))$ for all $\sigma, \tau$ and all $v$. The conclusion is that the $L$-submodule of $V$ spanned by the set of vectors $v$ with $\rho(\sigma)(v) = v$ for every $\sigma$ is all of $V$. Note that $\rho$ is only assumed to consist of additive maps, not of $L$-linear or $K$-linear ones, and that no finiteness assumption is made on $V$.
--
--   This is the elementary spanning half of Galois descent for vector spaces: the $K$-subspace of invariants of a semilinear Galois action generates $V$ over $L$, the concrete form of $L \otimes_K V^{G} \cong V$. It is used to produce bases of invariant vectors, via [`Module.exists_basis_forall_semilinear_apply_eq_of_isGalois`](thm.html#Module.exists_basis_forall_semilinear_apply_eq_of_isGalois), and in the construction of $q$-expansion bases with coefficients in a subfield for modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Submodule_span_fixedPoints_semilinear_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Submodule.span_fixedPoints_semilinear_eq_top
    (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (V : Type*) [AddCommGroup V] [Module L V] [Module K V] [IsScalarTower K L V]
    (ρ : (L ≃ₐ[K] L) → V →+ V)
    (hρ_smul : ∀ (σ : L ≃ₐ[K] L) (a : L) (v : V), ρ σ (a • v) = σ a • ρ σ v)
    (hρ_one : ∀ v : V, ρ 1 v = v)
    (hρ_mul : ∀ (σ τ : L ≃ₐ[K] L) (v : V), ρ (σ * τ) v = ρ σ (ρ τ v)) :
    Submodule.span L {v : V | ∀ σ : L ≃ₐ[K] L, ρ σ v = v} = ⊤ := by sorry
