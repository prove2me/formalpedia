-- Prove2me | Theorems.Thm_ValuationSubring_sub_one_mul_sum_smul_eq_zero_of_corner_decomposition
-- name    : ValuationSubring.sub_one_mul_sum_smul_eq_zero_of_corner_decomposition
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/d2ea74a3-bc73-54a0-84cb-2a68ae808dd5
-- title:
--   Frobenius constraint (χ₂(σ)²-1)sum nᵢ aᵢ = 0 on a decomposed corner
-- statement:
--   Let $p$ be a prime with $p \neq 2$, let $N \in \mathbb{N}$, and let $P$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` such that the image of $p$ is a non-unit of $P$ (the predicate `LiesOverPrime`). Let $\zeta$ be a primitive $p^N$-th root of unity. Let $A$ be a commutative ring and $\chi_1, \chi_2, c \colon \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to A$ functions such that $\chi_1$ and $\chi_2$ are multiplicative on the decomposition subgroup $D$ of $P$ over $\mathbb{Q}$, that $c(gh) = \chi_1(g)c(h) + c(g)\chi_2(h)$ for $g, h \in D$, that $\chi_1$ and $\chi_2$ take unit values on $D$, that $\chi_2(\tau) = 1$ for every $\tau$ in the image of the inertia subgroup of $P$ inside $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (written $I$ below), and that $\chi_1(g)\chi_2(g) = (e : A)$ whenever $g \in D$, $e \in \mathbb{N}$ and $g\zeta = \zeta^e$. Let $t \in \mathbb{N}$ and let $n \colon \mathrm{Fin}\,t \to \mathbb{N}$, $u, \beta \colon \mathrm{Fin}\,t \to \overline{\mathbb{Q}}$, $a \colon \mathrm{Fin}\,t \to A$ be such that each $u_i$ has $P$-valuation $1$ and is fixed by every element of $I$, and $\beta_i^{p^N} = p^{n_i} u_i$. Assume the corner is decomposed: for every $\tau \in I$ acting trivially on all $p^N$-th roots of unity and every $k \colon \mathrm{Fin}\,t \to \mathbb{N}$ with $\tau(\beta_i) = \zeta^{k_i}\beta_i$ for all $i$, one has $c(\tau) = \sum_i k_i \cdot a_i$. Then for every $\sigma \in D$ and $e \in \mathbb{N}$ with $\sigma\zeta = \zeta^e$, $$(\chi_2(\sigma)^2 - 1)\sum_i n_i \cdot a_i = 0.$$
--
--   This is the entry-level form of Wiles' relation $(\tilde\alpha^2 - 1)\sum_i n_i a_i = 0$ for the upper-triangular local representation at $p$: the hypotheses record an upper-triangular cocycle on the decomposition group at $P$ whose corner entry is given, on the inertia elements fixing $\mu_{p^N}$, by Kummer exponents of the radicands $p^{n_i}u_i$ with coefficients $a_i$, and the conclusion constrains $\sum_i n_i a_i$ by the action of $\sigma$ on $\zeta$. It is used in the construction of local invariants attached to an ordinary line in the deformation-ring data, via [`GaloisRep.DeformationRingData.exists_localInvariant_of_ordinaryLine`](thm.html#GaloisRep.DeformationRingData.exists_localInvariant_of_ordinaryLine).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_sub_one_mul_sum_smul_eq_zero_of_corner_decomposition.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped BigOperators

theorem ValuationSubring.sub_one_mul_sum_smul_eq_zero_of_corner_decomposition
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (N : ℕ) (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (ζ : (AlgebraicClosure ℚ)) (hζ : IsPrimitiveRoot ζ (p ^ N))
    {A : Type} [CommRing A] (χ₁ χ₂ c : ((AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) → A)
    (hχ₁ : ∀ g ∈ P.decompositionSubgroup ℚ, ∀ h ∈ P.decompositionSubgroup ℚ, χ₁ (g * h) = χ₁ g * χ₁ h)
    (hχ₂ : ∀ g ∈ P.decompositionSubgroup ℚ, ∀ h ∈ P.decompositionSubgroup ℚ, χ₂ (g * h) = χ₂ g * χ₂ h)
    (hc : ∀ g ∈ P.decompositionSubgroup ℚ, ∀ h ∈ P.decompositionSubgroup ℚ, c (g * h) = χ₁ g * c h + c g * χ₂ h)
    (hχ₁u : ∀ g ∈ P.decompositionSubgroup ℚ, IsUnit (χ₁ g)) (hχ₂u : ∀ g ∈ P.decompositionSubgroup ℚ, IsUnit (χ₂ g))
    (hχ₂I : ∀ τ ∈ P.inertiaSubgroupIn ℚ, χ₂ τ = 1)
    (hdet : ∀ g ∈ P.decompositionSubgroup ℚ, ∀ e : ℕ, g ζ = ζ ^ e → χ₁ g * χ₂ g = e)
    {t : ℕ} (n : Fin t → ℕ) (u β : Fin t → (AlgebraicClosure ℚ)) (a : Fin t → A)
    (hu : ∀ i, P.valuation (u i) = 1) (huI : ∀ i, ∀ σ ∈ P.inertiaSubgroupIn ℚ, σ (u i) = u i)
    (hβ : ∀ i, β i ^ p ^ N = (p : (AlgebraicClosure ℚ)) ^ (n i) * u i)
    (hdec : ∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : (AlgebraicClosure ℚ), ξ ^ p ^ N = 1 → τ ξ = ξ) →
      ∀ k : Fin t → ℕ, (∀ i, τ (β i) = ζ ^ (k i) * β i) → c τ = ∑ i, (k i) • a i)
    (σ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) (hσ : σ ∈ P.decompositionSubgroup ℚ) (e : ℕ) (hσζ : σ ζ = ζ ^ e) :
    (χ₂ σ ^ 2 - 1) * ∑ i, (n i) • a i = 0 := by sorry
