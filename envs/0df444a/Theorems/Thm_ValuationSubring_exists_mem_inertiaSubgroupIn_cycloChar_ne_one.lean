-- Prove2me | Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cycloChar_ne_one
-- name    : ValuationSubring.exists_mem_inertiaSubgroupIn_cycloChar_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/7e676ba1-9ad5-5878-9b53-24e9bb06ab9d
-- title:
--   Nontrivial characters of (ℤ/m)^× detect inertia at q
-- statement:
--   Let $q$ be a prime number and let $m$ be a natural number such that either $q$ is odd and $m = q$, or $q = 2$ and $m = 8$. Let $\mathrm{cyc}$ be a monoid homomorphism from the group of $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ to $(\mathbb{Z}/m)^\times$ which computes the action on $m$-th roots of unity, in the sense that for every automorphism $\sigma$ and every $\mu$ in the algebraic closure with $\mu^m = 1$ one has $\sigma\mu = \mu^{v}$, where $v$ is the canonical representative in $\{0,\dots,m-1\}$ of the residue class $\mathrm{cyc}(\sigma) \in \mathbb{Z}/m$. Let $K$ be a field and let $\chi : (\mathbb{Z}/m)^\times \to K^\times$ be a monoid homomorphism which is not the trivial homomorphism. Then for every valuation subring $A$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ such that the image of $q$ in the algebraic closure is a nonunit of $A$ (the predicate `LiesOverPrime`), there exists an automorphism $\sigma$ lying in `A.inertiaSubgroupIn ℚ`, that is, in the image of the inertia subgroup of $A$ under the inclusion of the decomposition subgroup of $A$ into the full automorphism group, with $\chi(\mathrm{cyc}(\sigma)) \neq 1$.
--
--   This is the arithmetic input expressing that $\mathbb{Q}(\mu_m)/\mathbb{Q}$ is totally ramified at $q$ for $m = q$ odd prime and for $m = 8$, $q = 2$, so that inertia at any place above $q$ covers all of $(\mathbb{Z}/m)^\times$ through the cyclotomic character and hence is not annihilated by any nontrivial character of $(\mathbb{Z}/m)^\times$. It is used in the vanishing statement [`groupCohomology.continuousH2S_ofChar_cycloChar_eq_zero_of_not_mem`](thm.html#groupCohomology.continuousH2S_ofChar_cycloChar_eq_zero_of_not_mem), where a twisting character must be shown to act nontrivially on inertia at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cycloChar_ne_one.lean

import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_cycloChar_ne_one
    (q : ℕ) (hq : q.Prime) (m : ℕ) (hm : (Odd q ∧ m = q) ∨ (q = 2 ∧ m = 8))
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod m)ˣ)
    (hcyc : ∀ σ (μ : AlgebraicClosure ℚ), μ ^ m = 1 → σ μ = μ ^ ((cyc σ : ZMod m)).val)
    {K : Type} [Field K] (χ : (ZMod m)ˣ →* Kˣ) (hχ : χ ≠ 1) :
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
      ∃ σ ∈ A.inertiaSubgroupIn ℚ, χ (cyc σ) ≠ 1 := by sorry
