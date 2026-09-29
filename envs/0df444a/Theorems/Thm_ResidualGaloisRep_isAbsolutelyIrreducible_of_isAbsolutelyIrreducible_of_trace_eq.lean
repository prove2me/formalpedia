-- Prove2me | Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_trace_eq
-- name    : ResidualGaloisRep.isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_trace_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/ae621ef1-7292-53d8-a8ac-8bbd80925bfe
-- title:
--   Trace equality transfers absolute irreducibility in dimension 2
-- statement:
--   Let $k$ be a field and let $\rho_1,\rho_2$ be two objects of type [`ResidualGaloisRep k`](def/GaloisRep_Residual.html#L22): each consists of a $k$-vector space $V$ with $\dim_k V = 2$, a monoid homomorphism $\rho$ from the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ` to $\operatorname{End}_k V$, and a witness that $\rho$ factors through a finite level, i.e. an intermediate field $L$ of `AlgebraicClosure ℚ` over $\mathbb{Q}$ with $L/\mathbb{Q}$ finite such that $\rho(\sigma) = 1$ for every $\sigma$ fixing $L$ pointwise. Assume $\rho_1$ is absolutely irreducible in the sense of the project, namely that after base change to `AlgebraicClosure k` — the representation on $\overline{k} \otimes_k \rho_1.V$ given by $\sigma \mapsto (\rho_1.\rho\,\sigma) \otimes \mathrm{id}$ — the only submodules of $\overline{k} \otimes_k \rho_1.V$ stable under all these operators are $\bot$ and $\top$. Assume further that for every automorphism $\sigma$ the $k$-linear traces agree, $\operatorname{tr}_{k}(\rho_1.\rho\,\sigma) = \operatorname{tr}_{k}(\rho_2.\rho\,\sigma)$. Then $\rho_2$ is absolutely irreducible in the same sense. No hypothesis is placed on the characteristic of $k$, and the representations are not assumed to be related beyond the equality of their trace functions.
--
--   This is the two-dimensional case of the fact, going back to Frobenius and Schur, that over an arbitrary field the trace function of a representation with open kernel detects absolute irreducibility; in characteristic $2$ it is genuinely stronger than the corresponding statement for characteristic polynomials, which the trace no longer determines. It is used in the construction of the ordinary line for $p$-adic representations attached to eigenforms, via the criterion that absolute irreducibility is equivalent to the operators $\rho(\sigma)$ spanning the full endomorphism algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ResidualGaloisRep_isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_trace_eq.lean

import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Module LinearMap

theorem ResidualGaloisRep.isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_trace_eq
    {k : Type} [Field k] (ρ₁ ρ₂ : ResidualGaloisRep k) (h₁ : ρ₁.IsAbsolutelyIrreducible)
    (htr : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      trace k ρ₁.V (ρ₁.ρ σ) = trace k ρ₂.V (ρ₂.ρ σ)) :
    ρ₂.IsAbsolutelyIrreducible := by sorry
