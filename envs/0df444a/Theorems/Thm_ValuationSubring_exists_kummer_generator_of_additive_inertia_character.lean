-- Prove2me | Theorems.Thm_ValuationSubring_exists_kummer_generator_of_additive_inertia_character
-- name    : ValuationSubring.exists_kummer_generator_of_additive_inertia_character
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/135ba7c6-9ae4-5c56-85e7-2af3a7b34ff7
-- title:
--   Additive inertia characters are Kummer characters
-- statement:
--   Let $p$ be a prime and let $n \le N$ be natural numbers. Let $P$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$, in the sense that $p$, viewed in $\overline{\mathbb Q}$, is a non-unit of $P$; write $I_P$ for `P.inertiaSubgroupIn ℚ`, the image in $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ of the inertia subgroup of $P$ under the inclusion of its decomposition subgroup. Let $\zeta \in \overline{\mathbb Q}$ be a primitive $p^N$-th root of unity, and let $\chi$ be any function from $\mathrm{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\mathbb Z/p^n$ subject to two hypotheses: (i) there is an intermediate field $F$ of $\overline{\mathbb Q}/\mathbb Q$, finite over $\mathbb Q$, such that $\chi(\tau s) = \chi(\tau)$ whenever $\tau, s \in I_P$ and $s$ fixes $F$ pointwise; and (ii) $\chi(\tau\tau') = \chi(\tau) + \chi(\tau')$ for all $\tau, \tau' \in I_P$ that both fix every $\xi \in \overline{\mathbb Q}$ with $\xi^{p^N} = 1$. Then there exist $x, \gamma \in \overline{\mathbb Q}$ with $x \neq 0$, such that $x$ is fixed by every $\sigma \in I_P$ fixing all $p^N$-th roots of unity, such that $\gamma^{p^n} = x$, and such that for every $\tau \in I_P$ fixing all $p^N$-th roots of unity and every natural number $k$, the relation $\tau\gamma = (\zeta^{p^{N-n}})^k \gamma$ forces $\chi(\tau) = k$ in $\mathbb Z/p^n$.
--
--   This is the Kummer-theoretic realisation of an additive, level-finite $\mathbb Z/p^n$-valued character of inertia at $p$: over the field fixed by the subgroup of $I_P$ acting trivially on $\mu_{p^N}$, the character becomes the Kummer cocycle of a radicand $x$, read multiplicatively through the root of unity $\zeta^{p^{N-n}}$. It is obtained from [`groupCohomology.Kummer.exists_kummerCocycle_eq_of_monoidHom_fixingSubgroup`](thm.html#groupCohomology.Kummer.exists_kummerCocycle_eq_of_monoidHom_fixingSubgroup) and feeds [`ValuationSubring.exists_inertia_fixed_kummer_generator_of_additive_character`](thm.html#ValuationSubring.exists_inertia_fixed_kummer_generator_of_additive_character), where the radicand is normalised further.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_kummer_generator_of_additive_inertia_character.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_kummer_generator_of_additive_inertia_character
    (p : ℕ) (hp : p.Prime) (N n : ℕ) (hn : n ≤ N)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (p ^ N))
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ZMod (p ^ n))
    (hlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ s ∈ P.inertiaSubgroupIn ℚ, s ∈ F.fixingSubgroup → χ (τ * s) = χ τ)
    (hadd : ∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ τ' ∈ P.inertiaSubgroupIn ℚ,
      (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
      (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ' ξ = ξ) → χ (τ * τ') = χ τ + χ τ') :
    ∃ x γ : AlgebraicClosure ℚ, x ≠ 0 ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → σ ξ = ξ) → σ x = x) ∧ γ ^ p ^ n = x ∧
      ∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) →
        ∀ k : ℕ, τ γ = (ζ ^ p ^ (N - n)) ^ k * γ → χ τ = k := by sorry
