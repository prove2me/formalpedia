-- Prove2me | Theorems.Thm_ResidualGaloisRep_charpoly_eq_of_charpoly_frobenius_eq
-- name    : ResidualGaloisRep.charpoly_eq_of_charpoly_frobenius_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/fdfe2fc6-9795-5e08-91aa-7c25f0bafc37
-- title:
--   Charpolys agree everywhere from agreement at unramified Frobenii
-- statement:
--   Fix a field $k$ and assume `hFD`: for every number field $M$ that is Galois over $\mathbb{Q}$ the predicate [`FrobeniusDensity.Statement M`](def/TaylorWiles_Primes.html#L72) holds, i.e. for every $\sigma \in \mathrm{Gal}(M/\mathbb{Q})$ and every finite set $S$ of naturals there is a prime $\ell \notin S$ such that for every prime ideal $Q$ of $\mathcal{O}_M$ over the rational prime $\ell$ with finite residue ring, some power $\sigma^{m}$ with $m$ coprime to $\mathrm{ord}(\sigma)$ is conjugate to the arithmetic Frobenius at $Q$. Let $\rho_1, \rho_2$ be two terms of [`ResidualGaloisRep k`](def/GaloisRep_Residual.html#L22), each consisting of a $k$-vector space $V$ of rank $2$, a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (the $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`) to $\mathrm{End}_k V$, and the condition that $\rho$ factors through a finite level: there is an intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, with $\rho(\tau) = 1$ whenever $\tau$ fixes $L$ pointwise. Let $S$ be a finite set of naturals, and suppose that for every prime $\ell \notin S$, every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a nonunit of $A$, and every $\tau$ lying in the decomposition subgroup of $A$ over $\mathbb{Q}$ and acting on the residue field of $A$ by $x \mapsto x^{\ell}$, the characteristic polynomials of $\rho_1(\tau)$ and $\rho_2(\tau)$ coincide. Then for every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ the characteristic polynomials of $\rho_1(\sigma)$ and $\rho_2(\sigma)$ coincide.
--
--   This is the Čebotarev/Frobenius-density comparison step: two two-dimensional residual representations with the same characteristic polynomials at Frobenius elements outside a finite set of primes have the same characteristic polynomials at every element of the absolute Galois group. It is conditional on the density statement [`FrobeniusDensity.Statement`](def/TaylorWiles_Primes.html#L72), carried as the hypothesis `hFD`, and is used downstream to identify residual representations attached to newforms with those attached to elliptic curves, and in the level-lowering and modularity-lifting arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_charpoly_eq_of_charpoly_frobenius_eq.lean

import Definitions.Def_TaylorWiles_Primes
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_GaloisRep_Residual
import Mathlib.LinearAlgebra.Charpoly.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NumberField Pointwise

theorem ResidualGaloisRep.charpoly_eq_of_charpoly_frobenius_eq
    (hFD : ∀ (M : Type) [Field M] [NumberField M] [IsGalois ℚ M], FrobeniusDensity.Statement M)
    {k : Type} [Field k] (ρ₁ ρ₂ : ResidualGaloisRep k) (S : Finset ℕ)
    (hfrob : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.LiesOverPrime ℓ → A.IsFrobeniusAt τ ℓ →
        (ρ₁.ρ τ).charpoly = (ρ₂.ρ τ).charpoly)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (ρ₁.ρ σ).charpoly = (ρ₂.ρ σ).charpoly := by sorry
