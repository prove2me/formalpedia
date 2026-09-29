-- Prove2me | Theorems.Thm_ValuationSubring_inertiaCharacter_eq_one_of_apply_kummerRoot_eq
-- name    : ValuationSubring.inertiaCharacter_eq_one_of_apply_kummerRoot_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/d1c57fd6-9f18-5f38-a8ac-bd88b7d201ea
-- title:
--   Inertia characters of exponent n vanish on stabilisers of q^{1/n}
-- statement:
--   Let $q$ be a prime number and let $P$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` lying over $q$ in the sense that the image of $q$ in $\overline{\mathbb Q}$ is a non-unit of $P$. Let $n$ be a positive integer coprime to $q$, and let $\alpha \in \overline{\mathbb Q}$ satisfy $\alpha^n = q$. Write $I_P \le \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ for the image of the inertia subgroup of $P$ over $\mathbb Q$ under the inclusion of the decomposition subgroup of $P$ over $\mathbb Q$ into the group of $\mathbb Q$-algebra automorphisms of $\overline{\mathbb Q}$. Let $A$ be a commutative group and let $\xi$ be an arbitrary function from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $A$ subject to three conditions: $\xi(\sigma\tau) = \xi(\sigma)\xi(\tau)$ for all $\sigma, \tau \in I_P$; $\xi(\sigma)^n = 1$ for all $\sigma \in I_P$; and there exists an intermediate field $L$ of $\mathbb Q \subseteq \overline{\mathbb Q}$, finite-dimensional over $\mathbb Q$, such that $\xi(\sigma) = 1$ for every $\sigma \in I_P$ fixing $L$ pointwise. Then for every $\sigma \in I_P$ with $\sigma(\alpha) = \alpha$ one has $\xi(\sigma) = 1$.
--
--   This is the Kummer-theoretic form of the procyclicity of tame inertia: a character of $I_P$ of exponent $n$ prime to $q$ which is trivial on the inertia elements acting trivially on some number field is determined by the Kummer character $\sigma \mapsto \sigma(\alpha)/\alpha$ attached to an $n$-th root $\alpha$ of $q$, so it dies on the stabiliser of $\alpha$. It is used, with $n = q-1$, by [`ValuationSubring.inertiaCharacter_eq_one_of_cyclotomic_eq_one`](thm.html#ValuationSubring.inertiaCharacter_eq_one_of_cyclotomic_eq_one) in the local analysis at $q$ of the ramification of the Frey curve's mod-$\ell$ representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_inertiaCharacter_eq_one_of_apply_kummerRoot_eq.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.inertiaCharacter_eq_one_of_apply_kummerRoot_eq {q : ℕ} (hq : q.Prime)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {n : ℕ} (hn0 : 0 < n) (hn : n.Coprime q) (α : AlgebraicClosure ℚ) (hα : α ^ n = (q : AlgebraicClosure ℚ))
    {A : Type} [CommGroup A] (ξ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → A)
    (hmul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ τ ∈ P.inertiaSubgroupIn ℚ, ξ (σ * τ) = ξ σ * ξ τ)
    (hexp : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ξ σ ^ n = 1)
    (hcont : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, (∀ x ∈ L, σ x = x) → ξ σ = 1)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (hfix : σ α = α) :
    ξ σ = 1 := by sorry
