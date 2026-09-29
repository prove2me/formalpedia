-- Prove2me | Theorems.Thm_ValuationSubring_valuation_eq_valuation_pow_of_mem_pow_of_not_mem_pow_succ
-- name    : ValuationSubring.valuation_eq_valuation_pow_of_mem_pow_of_not_mem_pow_succ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/b69317fb-9a58-5402-8d3f-bf8f0f55f467
-- title:
--   A place of ℚ̄ computes the Q-adic order
-- statement:
--   Let $P$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ`, with associated valuation `P.valuation` taking values in the value group of $P$, and let $M$ be a number field equipped with an algebra structure over $\overline{\mathbb Q}$, i.e. with a ring map $M \to \overline{\mathbb Q}$. Let $\mathfrak Q$ be a maximal ideal of the ring of integers $\mathcal O_M$. Assume that $P$ dominates $\mathcal O_M$ in the following explicit sense: the valuation of the image of every $x \in \mathcal O_M$ is at most $1$ (hypothesis `hQle`), and for $x \in \mathcal O_M$ membership in $\mathfrak Q$ holds if and only if the valuation of the image of $x$ is strictly less than $1$ (hypothesis `hQlt`), so that $\mathfrak Q$ is the centre of $P$ on $\mathcal O_M$. Let $\pi \in \mathcal O_M$ satisfy $\pi \in \mathfrak Q$ and $\pi \notin \mathfrak Q^2$, let $n$ be a natural number, and let $x \in \mathcal O_M$ satisfy $x \in \mathfrak Q^n$ and $x \notin \mathfrak Q^{n+1}$. Then the valuation of the image of $x$ equals the $n$-th power of the valuation of the image of $\pi$, the power being taken in the (multiplicative) value group of $P$.
--
--   The statement says that the restriction of a place of $\overline{\mathbb Q}$ to a number field it dominates is the $\mathfrak Q$-adic valuation, normalised so that a uniformiser $\pi$ of $\mathfrak Q$ has valuation `P.valuation (algebraMap M _ π)`. It is used by [`ValuationSubring.exists_valuation_mul_zpow_eq_one_of_forall_inertia_apply_eq`](thm.html#ValuationSubring.exists_valuation_mul_zpow_eq_one_of_forall_inertia_apply_eq), where it is applied to a number field and to a subfield of it in order to compare the two normalisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_valuation_eq_valuation_pow_of_mem_pow_of_not_mem_pow_succ.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem ValuationSubring.valuation_eq_valuation_pow_of_mem_pow_of_not_mem_pow_succ
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (M : Type) [Field M] [NumberField M] [Algebra M (AlgebraicClosure ℚ)]
    (Q : Ideal (𝓞 M)) [Q.IsMaximal]
    (hQle : ∀ x : 𝓞 M, P.valuation (algebraMap M (AlgebraicClosure ℚ) x) ≤ 1)
    (hQlt : ∀ x : 𝓞 M, x ∈ Q ↔ P.valuation (algebraMap M (AlgebraicClosure ℚ) x) < 1)
    (π : 𝓞 M) (hπ : π ∈ Q) (hπ2 : π ∉ Q ^ 2)
    (n : ℕ) (x : 𝓞 M) (hx : x ∈ Q ^ n) (hx' : x ∉ Q ^ (n + 1)) :
    P.valuation (algebraMap M (AlgebraicClosure ℚ) x) = P.valuation (algebraMap M (AlgebraicClosure ℚ) π) ^ n := by sorry
