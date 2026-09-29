-- Prove2me | Theorems.Thm_ValuationSubring_exists_kummer_decomposition_of_inertia_cocycle
-- name    : ValuationSubring.exists_kummer_decomposition_of_inertia_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/bf30b67f-436c-59a9-82f4-b6d325754b98
-- title:
--   Kummer decomposition of an additive equivariant inertia cocycle
-- statement:
--   Let $p$ be a prime with $p \neq 2$, let $N$ be a natural number, and let $P$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` whose nonunits contain the image of $p$, so that $P$ lies over $p$. Write $I_P$ for the subgroup of $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ obtained as the image of the inertia subgroup of $P$ inside the decomposition subgroup of $P$ over $\mathbb{Q}$, pushed forward along the inclusion of that decomposition subgroup. Let $\zeta \in \overline{\mathbb{Q}}$ be a primitive $p^N$-th root of unity, let $M$ be a finite additive commutative group with $p^N m = 0$ for all $m \in M$, and let $c$ be an arbitrary function from the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$ to $M$ satisfying three conditions: (i) there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that $c(\tau s) = c(\tau)$ whenever $\tau, s \in I_P$ and $s$ lies in the fixing subgroup of $F$; (ii) $c(\tau\tau') = c(\tau) + c(\tau')$ whenever $\tau, \tau' \in I_P$ both fix every $\xi$ with $\xi^{p^N} = 1$; (iii) for $\sigma \in I_P$ and $a \in \mathbb{N}$ with $\sigma\zeta = \zeta^a$, and for $\tau \in I_P$ fixing all $p^N$-th roots of unity, $c(\sigma\tau\sigma^{-1}) = a \cdot c(\tau)$. Then there exist a natural number $t$, families $x, \beta : \mathrm{Fin}\, t \to \overline{\mathbb{Q}}$ and $a : \mathrm{Fin}\, t \to M$ such that each $x_i$ is non-zero and fixed by every element of $I_P$, each $\beta_i$ satisfies $\beta_i^{p^N} = x_i$, and for every $\tau \in I_P$ fixing all $p^N$-th roots of unity and every $k : \mathrm{Fin}\, t \to \mathbb{N}$ with $\tau(\beta_i) = \zeta^{k_i}\beta_i$ for all $i$, one has $c(\tau) = \sum_i k_i \cdot a_i$.
--
--   This is the multi-coordinate form of Kummer theory over the fixed field of inertia at $p$: an additive, cyclotomically equivariant, locally constant inertia cocycle with finite values is expressed through the Kummer exponents of finitely many inertia-fixed radicands with chosen $p^N$-th roots. It feeds the local analysis of ordinary lines, being cited by [`GaloisRep.DeformationRingData.exists_localInvariant_of_ordinaryLine`](thm.html#GaloisRep.DeformationRingData.exists_localInvariant_of_ordinaryLine).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_kummer_decomposition_of_inertia_cocycle.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_kummer_decomposition_of_inertia_cocycle
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (N : ℕ)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (p ^ N))
    {M : Type} [AddCommGroup M] [Finite M] (hM : ∀ m : M, (p ^ N) • m = 0)
    (c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M)
    (hlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ s ∈ P.inertiaSubgroupIn ℚ, s ∈ F.fixingSubgroup → c (τ * s) = c τ)
    (hadd : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ τ' ∈ P.inertiaSubgroupIn ℚ,
      (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
      (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ' ξ = ξ) → c (τ * τ') = c τ + c τ')
    (hconj : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ, σ ζ = ζ ^ a →
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
        c (σ * τ * σ⁻¹) = a • c τ) :
    ∃ (t : ℕ) (x β : Fin t → AlgebraicClosure ℚ) (a : Fin t → M),
      (∀ i, x i ≠ 0) ∧ (∀ i, ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ (x i) = x i) ∧ (∀ i, β i ^ p ^ N = x i) ∧
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
        ∀ k : Fin t → ℕ, (∀ i, τ (β i) = ζ ^ (k i) * β i) → c τ = ∑ i, (k i) • a i := by sorry
