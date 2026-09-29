-- Prove2me | Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq
-- name    : ResidualGaloisRep.isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/23bb08c6-ce86-5f01-a457-1034927c3e21
-- title:
--   Absolute irreducibility transfers along equal characteristic polynomials
-- statement:
--   Let $k$ be a field and let $\rho_1,\rho_2$ be two objects of type [`ResidualGaloisRep k`](def/GaloisRep_Residual.html#L22): each consists of a $k$-vector space $V$ with $\dim_k V = 2$, a monoid homomorphism $\rho$ from the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ` to $\operatorname{End}_k(V)$, and a witness that $\rho$ factors through a finite level, i.e. there is an intermediate field $L$ of $\mathbb{Q} \subseteq \overline{\mathbb{Q}}$ with $L/\mathbb{Q}$ finite-dimensional such that $\rho(\sigma) = 1$ for every $\sigma$ fixing $L$ pointwise. Assume $\rho_1$ is absolutely irreducible in the sense of the project: after base change to `AlgebraicClosure k`, i.e. for the representation $\sigma \mapsto \rho_1(\sigma) \otimes \mathrm{id}$ on $\overline{k} \otimes_k V_1$, every submodule $W$ stable under all the operators $\rho_1(\sigma)$ satisfies $W = \bot$ or $W = \top$. Assume further that for every $\sigma$ the characteristic polynomials of the endomorphisms $\rho_1(\sigma)$ and $\rho_2(\sigma)$ coincide in $k[X]$. Then $\rho_2$ is absolutely irreducible in the same sense.
--
--   This is the transfer of absolute irreducibility along an equality of characteristic polynomials, in the circle of ideas of the Brauer–Nesbitt theorem; here only the two-dimensional case over a field $k$ and the one-sided implication are asserted. It is used throughout the treatment of Galois representations attached to cusp forms, for instance in the construction of flat or ordinary members of a family of such representations and in the deduction of a contradiction from ordinarity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq.lean

import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ResidualGaloisRep.isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq
    {k : Type} [Field k] (ρ₁ ρ₂ : ResidualGaloisRep k) (h₁ : ρ₁.IsAbsolutelyIrreducible)
    (hcp : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (ρ₁.ρ σ).charpoly = (ρ₂.ρ σ).charpoly) :
    ρ₂.IsAbsolutelyIrreducible := by sorry
