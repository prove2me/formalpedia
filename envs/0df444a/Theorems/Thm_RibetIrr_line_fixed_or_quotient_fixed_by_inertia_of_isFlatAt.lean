-- Prove2me | Theorems.Thm_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt
-- name    : RibetIrr.line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/145c012c-e078-501d-b0c6-b7a0df5faf28
-- title:
--   Inertia at p fixes a stable line or its quotient
-- statement:
--   Let $p$ be a prime, let $\mathcal{O}'$ be a discrete valuation ring (a commutative domain that is a discrete valuation ring) with fraction field $K$, and let $\rho$ be a two-dimensional adic Galois representation over $\mathcal{O}'$: a finite free $\mathcal{O}'$-module $V$ of rank $2$ together with a monoid homomorphism $\rho.\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, to $\mathrm{End}_{\mathcal{O}'}(V)$, continuous in the adic sense that for each $n$ there is a finite extension $L/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ with $\rho(\sigma)v-v\in \mathfrak{m}^n V$ for all $v\in V$ and all $\sigma$ fixing $L$ pointwise. Assume: (i) `ρ.IsFlatAt p`, i.e. the residue field of $\mathcal{O}'$ is finite and, for every ideal $I$ of $\mathcal{O}'$ with $\mathcal{O}'/I$ finite, there is a commutative cocommutative Hopf algebra $H$ over the subring $\mathbb{Z}_{(p)}\subset\mathbb{Q}$ of rationals with denominator coprime to $p$, module-finite and flat over it, and a bijection $e$ from the convolution group of $\mathbb{Z}_{(p)}$-algebra maps $H\to\overline{\mathbb{Q}}$ onto $V/IV$ carrying the convolution product to addition and intertwining the Galois action (if $g=\sigma\circ f$ pointwise on $H$, then $e(g)$ is the image of $e(f)$ under the induced action of $\sigma$ on $V/IV$); (ii) `ρ.DetIsCyclotomic p`, i.e. $p\in\mathfrak{m}$ and, whenever $\sigma$ raises every $p^n$-th root of unity to the power $a\in\mathbb{N}$, one has $\det\rho(\sigma)-a\in(p^n)$. Let $W$ be a $K$-submodule of $K\otimes_{\mathcal{O}'}V$ with $\dim_K W=1$, carried into itself by the base change of $\rho(\sigma)$ for every $\sigma$. Then one of the following holds: for every valuation subring $P$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $P$ and every $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$, the base change of $\rho(\sigma)$ fixes every $w\in W$; or, for every such $P$ and $\sigma$, the base change of $\rho(\sigma)$ satisfies $\rho(\sigma)v-v\in W$ for all $v\in K\otimes_{\mathcal{O}'}V$.
--
--   This is the local input at $p$ in the finite-flat case of Ribet's irreducibility argument: classically, the character cut out by a Galois-stable line in a representation coming from finite flat group schemes at $p$ is, on inertia at $p$, either trivial or cyclotomic, reflecting the fact that such a group scheme over the strict henselisation of $\mathbb{Z}_{(p)}$ is an extension of an étale by a multiplicative group scheme. It is used by [`RibetIrr.irreducible_of_point_of_not_dvd`](thm.html#RibetIrr.irreducible_of_point_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_RibetIrr_line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt.lean

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem RibetIrr.line_fixed_or_quotient_fixed_by_inertia_of_isFlatAt (p : ℕ) [Fact p.Prime]
    (𝒪' : Type) [CommRing 𝒪'] [IsDomain 𝒪'] [IsDiscreteValuationRing 𝒪']
    (K : Type) [Field K] [Algebra 𝒪' K] [IsFractionRing 𝒪' K]
    (ρ : GaloisRepAdic 𝒪') (hflat : ρ.IsFlatAt p) (hdet : ρ.DetIsCyclotomic p)
    (W : Submodule K (K ⊗[𝒪'] ρ.V)) (hW : Module.finrank K W = 1)
    (hWstab : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ w ∈ W,
      (ρ.ρ σ).baseChange K w ∈ W) :
    (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w ∈ W, (ρ.ρ σ).baseChange K w = w) ∨
    (∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
        ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : K ⊗[𝒪'] ρ.V, (ρ.ρ σ).baseChange K v - v ∈ W) := by sorry
