-- Prove2me | Theorems.Thm_ValuationSubring_exists_inertia_fixed_kummer_generator_of_additive_character
-- name    : ValuationSubring.exists_inertia_fixed_kummer_generator_of_additive_character
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/68ef270b-089d-5e65-8fe0-635105986885
-- title:
--   Cyclotomically equivariant Kummer character has inertia-fixed radicand
-- statement:
--   Let $p$ be a prime with $p \neq 2$, let $n \le N$ be natural numbers, and let $P$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` satisfying `P.LiesOverPrime p`, i.e. the image of $p$ is a nonunit of $P$. Write $I_P =$ `P.inertiaSubgroupIn ℚ` for the image of the inertia subgroup of $P$ over $\mathbb{Q}$ under the inclusion of the decomposition subgroup into $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$, and let $J_N \subseteq I_P$ denote the elements fixing every $\xi$ with $\xi^{p^N} = 1$. Let $\zeta$ be a primitive $p^N$-th root of unity and let $\chi$ be any function from $\mathbb{Q}$-automorphisms of $\overline{\mathbb{Q}}$ to $\mathbb{Z}/p^n$ subject to three hypotheses: (i) there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that $\chi(\tau s) = \chi(\tau)$ whenever $\tau, s \in I_P$ and $s$ lies in the fixing subgroup of $F$; (ii) $\chi(\tau\tau') = \chi(\tau) + \chi(\tau')$ for $\tau, \tau' \in J_N$; (iii) $\chi(\sigma\tau\sigma^{-1}) = a \cdot \chi(\tau)$ whenever $\sigma \in I_P$, $a \in \mathbb{N}$ with $\sigma\zeta = \zeta^a$, and $\tau \in J_N$. Then there exist $x, \gamma \in \overline{\mathbb{Q}}$ with $x \neq 0$, with $\sigma x = x$ for every $\sigma \in I_P$, with $\gamma^{p^n} = x$, and such that for every $\tau \in J_N$ and every $k \in \mathbb{N}$, $\tau\gamma = (\zeta^{p^{N-n}})^k \gamma$ implies $\chi(\tau) = k$.
--
--   This realises an additive, cyclotomically equivariant character of inertia as the Kummer character of a radicand fixed by the whole inertia group, rather than merely by the subgroup $J_N$ acting trivially on $\mu_{p^N}$; the equivariance hypothesis encodes that the class of the radicand in $K_N^\times/(K_N^\times)^{p^n}$ is Galois-stable over the inertia-fixed field, and $p$ odd is what makes the descent of the class available. It is used, one cyclic coordinate at a time, by [`ValuationSubring.exists_kummer_decomposition_of_inertia_cocycle`](thm.html#ValuationSubring.exists_kummer_decomposition_of_inertia_cocycle).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_inertia_fixed_kummer_generator_of_additive_character.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_inertia_fixed_kummer_generator_of_additive_character
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (N n : ℕ) (hn : n ≤ N)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (p ^ N))
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ZMod (p ^ n))
    (hlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ s ∈ P.inertiaSubgroupIn ℚ, s ∈ F.fixingSubgroup → χ (τ * s) = χ τ)
    (hadd : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ τ' ∈ P.inertiaSubgroupIn ℚ,
      (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
      (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ' ξ = ξ) → χ (τ * τ') = χ τ + χ τ')
    (hconj : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ, σ ζ = ζ ^ a →
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
        χ (σ * τ * σ⁻¹) = a • χ τ) :
    ∃ x γ : AlgebraicClosure ℚ, x ≠ 0 ∧ (∀ σ ∈ P.inertiaSubgroupIn ℚ, σ x = x) ∧ γ ^ p ^ n = x ∧
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
        ∀ k : ℕ, τ γ = (ζ ^ p ^ (N - n)) ^ k * γ → χ τ = k := by sorry
