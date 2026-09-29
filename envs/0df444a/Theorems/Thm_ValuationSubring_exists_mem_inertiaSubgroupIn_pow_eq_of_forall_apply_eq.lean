-- Prove2me | Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq
-- name    : ValuationSubring.exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/62ddc984-3156-59f7-868f-d0f7ad224fc1
-- title:
--   Inertia elements fixing all p-power roots of q are pⁿ-th powers
-- statement:
--   Let $p$ and $q$ be prime natural numbers with $p \neq q$, let $P$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` satisfying `P.LiesOverPrime q`, that is, the image of $q$ in $\overline{\mathbb{Q}}$ lies in the set of nonunits of $P$, and let $n$ be a natural number. Let $g$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$ lying in `P.inertiaSubgroupIn ℚ`, the image in the full automorphism group $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ of the inertia subgroup of $P$ over $\mathbb{Q}$ under the inclusion of the decomposition subgroup of $P$ over $\mathbb{Q}$. Assume further that $g$ fixes every $p$-power root of $q$: for every $\alpha \in \overline{\mathbb{Q}}$ and every natural number $k$ with $\alpha^{p^k} = q$ one has $g\alpha = \alpha$. Then $g$ is a $p^n$-th power inside the inertia group: there exists $w \in$ `P.inertiaSubgroupIn ℚ` with $w^{p^n} = g$.
--
--   This is the statement that the $p$-part of tame inertia at a place above $q$ is detected on the $p$-power roots of $q$: an inertia element fixing all of them is infinitely $p$-divisible within the inertia group. It is used in the construction of tame generators of inertia and in comparing inertia elements with Frobenius conjugates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq.lean

import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq
    {p q : ℕ} (hp : p.Prime) (hq' : q.Prime) (hpq : p ≠ q)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hq : P.LiesOverPrime q) (n : ℕ)
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hg : g ∈ P.inertiaSubgroupIn ℚ)
    (hrad : ∀ (α : AlgebraicClosure ℚ) (k : ℕ), α ^ (p ^ k) = (q : AlgebraicClosure ℚ) → g α = α) :
    ∃ w ∈ P.inertiaSubgroupIn ℚ, w ^ (p ^ n) = g := by sorry
