-- Prove2me | Theorems.Thm_ResidualGaloisRep_finrank_invariants_adZero_res_zpowers_eq_one_of_det_eq_neg_one
-- name    : ResidualGaloisRep.finrank_invariants_adZero_res_zpowers_eq_one_of_det_eq_neg_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/91091fcc-e75b-54d3-993f-47eea0cc7cc7
-- title:
--   Involutions of determinant -1 fix a line in ad⁰
-- statement:
--   Let $k$ be a field in which $2 \neq 0$, and let $\bar\rho$ be a residual Galois representation over $k$ in the sense of the project structure [`ResidualGaloisRep`](def/GaloisRep_Residual.html#L22): a $k$-vector space $V$ with $\dim_k V = 2$, a monoid homomorphism $\bar\rho \colon \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}}) \to \mathrm{End}_k(V)$ (where $\overline{\mathbb{Q}}$ is `AlgebraicClosure ℚ`), together with the condition that $\bar\rho$ factors through a finite level, i.e. there is an intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ with $L/\mathbb{Q}$ finite such that $\bar\rho(\sigma) = 1$ for every automorphism $\sigma$ fixing $L$ pointwise. Let $\sigma$ be an automorphism of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ with $\sigma^2 = 1$ and with $\det \bar\rho(\sigma) = -1$. Write $\mathrm{ad}^0\bar\rho$ for `ρbar.adZero`, the representation obtained by restricting the adjoint representation `ρbar.adRep` on $\mathrm{End}_k(V)$ to the invariant submodule $\ker(\mathrm{tr}_k \colon \mathrm{End}_k(V) \to k)$ of trace-zero endomorphisms. Then the $k$-dimension of the space of invariants of the restriction of $\mathrm{ad}^0\bar\rho$ along the inclusion of the subgroup $\langle\sigma\rangle$ of integer powers of $\sigma$ equals $1$.
--
--   This is the computation of the archimedean local term $h^0(\langle c\rangle, \mathrm{ad}^0\bar\rho) = 1$ for an involution of determinant $-1$ (complex conjugation in the odd case), in the shape needed for the Selmer-group estimates of the Taylor–Wiles argument. It is used in the proof of the bound on the strict Selmer group of $\mathrm{ad}^0\bar\rho$ in terms of the number of Taylor–Wiles primes and the dimension of the dual Selmer group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_finrank_invariants_adZero_res_zpowers_eq_one_of_det_eq_neg_one.lean

import Mathlib
import Definitions.Def_GaloisRep_AdZero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ResidualGaloisRep.finrank_invariants_adZero_res_zpowers_eq_one_of_det_eq_neg_one
    {k : Type} [Field k] (h2 : (2 : k) ≠ 0) (ρbar : ResidualGaloisRep k)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ * σ = 1)
    (hdet : LinearMap.det (ρbar.ρ σ) = -1) :
    Module.finrank k (Rep.res (Subgroup.zpowers σ).subtype ρbar.adZero).ρ.invariants = 1 := by sorry
