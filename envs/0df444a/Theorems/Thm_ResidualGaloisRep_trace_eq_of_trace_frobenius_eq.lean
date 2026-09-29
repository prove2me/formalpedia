-- Prove2me | Theorems.Thm_ResidualGaloisRep_trace_eq_of_trace_frobenius_eq
-- name    : ResidualGaloisRep.trace_eq_of_trace_frobenius_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/c5ae5dea-76a4-5cd1-a787-14eb6c462c50
-- title:
--   Traces determined by Frobenius traces outside a finite set
-- statement:
--   Let $k$ be a field and let $\rho_1,\rho_2$ be two objects of type [`ResidualGaloisRep k`](def/GaloisRep_Residual.html#L22): each consists of a $k$-vector space $V$ of rank $2$ together with a monoid homomorphism $\rho$ from $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q}) = \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\mathrm{End}_k(V)$ which factors through a finite level, i.e. there is an intermediate field $L$ of $\overline{\mathbb Q}/\mathbb Q$ with $[L:\mathbb Q]<\infty$ such that $\rho(\sigma)=1$ for every $\sigma$ fixing $L$ pointwise. Let $S$ be a finite set of natural numbers, and assume: for every prime $\ell\notin S$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $\ell$ a non-unit of $A$ (so $A$ lies over $\ell$), and every $\tau\in\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ lying in the decomposition subgroup of $A$ over $\mathbb Q$ and acting on the residue field of $A$ by $x\mapsto x^{\ell}$, one has $\mathrm{tr}\,\rho_1(\tau)=\mathrm{tr}\,\rho_2(\tau)$ (traces of $k$-linear endomorphisms of $\rho_1.V$, $\rho_2.V$ respectively). Then for every $\sigma\in\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ one has $\mathrm{tr}\,\rho_1(\sigma)=\mathrm{tr}\,\rho_2(\sigma)$.
--
--   This is the standard Chebotarev argument that the trace of a Galois representation with open kernel is determined by its values at Frobenius elements at the primes outside any finite set, traces being class functions on the relevant finite Galois group. It is used in the Taylor–Wiles level arguments, for instance in identifying residual representations attached to Hecke eigensystems and in the local analysis of unipotence on inertia.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_trace_eq_of_trace_frobenius_eq.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial IsLocalRing

theorem ResidualGaloisRep.trace_eq_of_trace_frobenius_eq
    {k : Type} [Field k] (ρ₁ ρ₂ : ResidualGaloisRep k) (S : Finset ℕ)
    (hfrob : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.LiesOverPrime ℓ → A.IsFrobeniusAt τ ℓ →
        LinearMap.trace k ρ₁.V (ρ₁.ρ τ) = LinearMap.trace k ρ₂.V (ρ₂.ρ τ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.trace k ρ₁.V (ρ₁.ρ σ) = LinearMap.trace k ρ₂.V (ρ₂.ρ σ) := by sorry
