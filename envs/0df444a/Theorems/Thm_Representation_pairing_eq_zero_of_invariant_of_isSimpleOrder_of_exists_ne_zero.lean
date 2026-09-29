-- Prove2me | Theorems.Thm_Representation_pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero
-- name    : Representation.pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/bc312fcc-1a5b-52b0-b539-53f9d47729ce
-- title:
--   Invariant pairing with an irreducible representation vanishes
-- statement:
--   Let $k$ be a commutative semiring and $K$ a group, let $S$, $S'$ and $X$ be additive commutative monoids equipped with $k$-module structures, and let $\rho$ be a representation of $K$ on $S$ and $\rho'$ a representation of $K$ on $S'$, both over $k$; assume the lattice of subrepresentations of $\rho'$ is a simple order, i.e. `Subrepresentation ρ'` has exactly the two elements $\bot$ and $\top$ and these are distinct. Let $\beta \colon S \to S' \to X$ be a $k$-bilinear map which is invariant in the sense that $\beta(\rho(g)s, \rho'(g)s') = \beta(s,s')$ for all $g \in K$, $s \in S$, $s' \in S'$. Assume further that some $s' \in S'$ is non-zero and satisfies $\beta(s,s') = 0$ for every $s \in S$. The conclusion is that $\beta$ is the zero bilinear map. Note that irreducibility is assumed of the second argument $\rho'$ only, and that no hypothesis of non-degeneracy on the $S$-side is imposed.
--
--   This is the kernel form of Schur's lemma for invariant bilinear pairings: an invariant pairing against an irreducible representation is either zero or has trivial right kernel. It is used in the theory of automorphic forms here, in [`AutomorphicForm.exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq`](thm.html#AutomorphicForm.exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Representation.pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero
    {k : Type*} [CommSemiring k] {K : Type*} [Group K]
    {S : Type*} [AddCommMonoid S] [Module k S] {S' : Type*} [AddCommMonoid S'] [Module k S']
    {X : Type*} [AddCommMonoid X] [Module k X]
    (ρ : Representation k K S) (ρ' : Representation k K S') [IsSimpleOrder (Subrepresentation ρ')]
    (β : S →ₗ[k] S' →ₗ[k] X) (hβ : ∀ (g : K) (s : S) (s' : S'), β (ρ g s) (ρ' g s') = β s s')
    (h0 : ∃ s' : S', s' ≠ 0 ∧ ∀ s : S, β s s' = 0) :
    β = 0 := by sorry
