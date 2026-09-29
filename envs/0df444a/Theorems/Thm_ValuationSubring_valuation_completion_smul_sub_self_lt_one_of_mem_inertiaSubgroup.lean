-- Prove2me | Theorems.Thm_ValuationSubring_valuation_completion_smul_sub_self_lt_one_of_mem_inertiaSubgroup
-- name    : ValuationSubring.valuation_completion_smul_sub_self_lt_one_of_mem_inertiaSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/01e349fe-6922-5469-8511-f7f1953eb6d2
-- title:
--   Inertia acts trivially on the residue field of the completion
-- statement:
--   Let $F$ and $K$ be fields with $K$ an $F$-algebra, and let $A$ be a valuation subring of $K$, with associated valuation $A.\mathrm{valuation}$ on $K$. Assume, as an instance hypothesis, the fact that $A$ is decomposition-isometric over $F$, i.e. that every $\sigma$ in the decomposition subgroup $A.\mathrm{decompositionSubgroup}\ F$ (the stabiliser of $A$ inside the $F$-algebra automorphisms of $K$) satisfies $A.\mathrm{valuation}(\sigma x) = A.\mathrm{valuation}(x)$ for all $x \in K$; consequently the decomposition subgroup acts on the completion $A.\mathrm{valuation}.\mathrm{Completion}$ of $K$ with respect to this valuation. Let $\sigma$ be an element of the decomposition subgroup lying in the inertia subgroup $A.\mathrm{inertiaSubgroup}\ F$, that is, in the kernel of the induced action on the residue field of $A$. Let $x$ be an element of the completion whose extended valuation satisfies $\mathrm{v}(x) \le 1$. Then the conclusion is the strict inequality $\mathrm{v}(\sigma \cdot x - x) < 1$ for the extended valuation on the completion.
--
--   This is the statement that the inertia subgroup of a valuation subring acts trivially on the residue field of the completion, the local–global dictionary item identifying inertia at $A$ with the inertia group of the completed field. It is used in the proof of [`ValuationSubring.exists_valuation_eq_zpow_and_exists_pow_eq_of_forall_inertia_smul_completion_eq`](thm.html#ValuationSubring.exists_valuation_eq_zpow_and_exists_pow_eq_of_forall_inertia_smul_completion_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_valuation_completion_smul_sub_self_lt_one_of_mem_inertiaSubgroup.lean

import Mathlib
import Definitions.Def_ValuationSubring_CompletionDecompositionAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.valuation_completion_smul_sub_self_lt_one_of_mem_inertiaSubgroup
    {F K : Type*} [Field F] [Field K] [Algebra F K] (A : ValuationSubring K)
    [Fact (A.DecompositionIsometric F)]
    {σ : A.decompositionSubgroup F} (hσ : σ ∈ A.inertiaSubgroup F)
    (x : A.valuation.Completion) (hx : Valued.v x ≤ 1) :
    Valued.v (σ • x - x) < 1 := by sorry
