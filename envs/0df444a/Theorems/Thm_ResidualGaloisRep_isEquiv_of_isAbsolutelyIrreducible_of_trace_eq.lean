-- Prove2me | Theorems.Thm_ResidualGaloisRep_isEquiv_of_isAbsolutelyIrreducible_of_trace_eq
-- name    : ResidualGaloisRep.isEquiv_of_isAbsolutelyIrreducible_of_trace_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/76beaade-b1a8-5e94-b47f-1b9b44b85672
-- title:
--   Equal traces imply equivalence for absolutely irreducible residual representations
-- statement:
--   Let $k$ be a field and let $\rho_1,\rho_2$ be residual Galois representations over $k$ in the sense of the structure [`ResidualGaloisRep`](def/GaloisRep_Residual.html#L22): each consists of a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism $\rho$ from the group of $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ to $\mathrm{End}_k(V)$ which factors through a finite level, i.e. there is an intermediate field $L$ of $\mathbb{Q} \subseteq \mathrm{AlgebraicClosure}\,\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that every $\sigma$ fixing $L$ pointwise has $\rho(\sigma) = 1$. Assume both are absolutely irreducible, meaning that after base change to $\mathrm{AlgebraicClosure}\,k$ (tensoring the carrier and extending each endomorphism) the only Galois-stable submodules of $\mathrm{AlgebraicClosure}\,k \otimes_k V$ are $\bot$ and $\top$. Assume further that for every $\sigma$ one has $\mathrm{tr}_k(\rho_1(\sigma)) = \mathrm{tr}_k(\rho_2(\sigma))$. The conclusion is that $\rho_1$ and $\rho_2$ are equivalent: there exists a $k$-linear isomorphism $e : \rho_1.V \to \rho_2.V$ with $e(\rho_1(\sigma)x) = \rho_2(\sigma)(e\,x)$ for all $\sigma$ and all $x$.
--
--   This is the Brauer–Nesbitt comparison principle in the form needed for two-dimensional residual Galois representations: an absolutely irreducible representation is determined up to isomorphism by its character. It is used in the residual-comparison steps of the modularity argument, and in particular is invoked by the variant [`ResidualGaloisRep.isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq`](thm.html#ResidualGaloisRep.isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq) in which equality of characteristic polynomials replaces equality of traces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_isEquiv_of_isAbsolutelyIrreducible_of_trace_eq.lean

import Definitions.Def_GaloisRep_ResidualEquiv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Module LinearMap

theorem ResidualGaloisRep.isEquiv_of_isAbsolutelyIrreducible_of_trace_eq
    {k : Type} [Field k] (ρ₁ ρ₂ : ResidualGaloisRep k)
    (h₁ : ρ₁.IsAbsolutelyIrreducible) (h₂ : ρ₂.IsAbsolutelyIrreducible)
    (htr : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      trace k ρ₁.V (ρ₁.ρ σ) = trace k ρ₂.V (ρ₂.ρ σ)) :
    ρ₁.IsEquiv ρ₂ := by sorry
