-- Prove2me | Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq_of_isGalois
-- name    : ValuationSubring.exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq_of_isGalois
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/04e8ca19-440e-5b9c-894c-828aae7a01c8
-- title:
--   Radical-fixing inertia elements are pⁿ-th powers in inertia
-- statement:
--   Let $k$ and $L$ be fields with $L$ an algebra over $k$, $L$ algebraically closed of characteristic zero and Galois over $k$, and assume every element of $L$ is algebraic over $\mathbb{Q}$. Let $p$ and $q$ be prime natural numbers with $p \neq q$, and let $P$ be a valuation subring of $L$ such that the image of $q$ in $L$ is a nonunit of $P$ (that is, $P$ lies over the rational prime $q$). Write $I_P \le (L \simeq_{\mathrm{alg}[k]} L)$ for the image, under the inclusion of the decomposition subgroup of $P$ over $k$ into the full group of $k$-algebra automorphisms of $L$, of the inertia subgroup of $P$ over $k$. Let $n$ be a natural number and let $g$ be a $k$-algebra automorphism of $L$ belonging to $I_P$, and suppose that $g$ fixes every $p$-power root of $q$ in $L$: for all $\alpha \in L$ and all $j \in \mathbb{N}$ with $\alpha^{p^{j}} = q$ one has $g\alpha = \alpha$. Then there exists $w \in I_P$ with $w^{p^{n}} = g$.
--
--   This is the $p$-divisibility statement for the subgroup of inertia at a place above $q \neq p$ consisting of elements fixing all $p$-power radicals of $q$, stated over an arbitrary base field $k$ rather than only over $\mathbb{Q}$; the extraction of $p^{n}$-th roots rests on a Kummer-descent statement for the valuation subring $P$. It is used in the construction of tame generators of inertia subgroups, [`ValuationSubring.exists_forall_tame_generator_inertiaSubgroupIn_of_isGalois`](thm.html#ValuationSubring.exists_forall_tame_generator_inertiaSubgroupIn_of_isGalois).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq_of_isGalois.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_mem_inertiaSubgroupIn_pow_eq_of_forall_apply_eq_of_isGalois
    {k L : Type} [Field k] [Field L] [Algebra k L] [IsAlgClosed L] [CharZero L] [IsGalois k L]
    (halg : ∀ x : L, IsAlgebraic ℚ x)
    {p q : ℕ} (hp : p.Prime) (hq' : q.Prime) (hpq : p ≠ q)
    (P : ValuationSubring L) (hq : P.LiesOverPrime q) (n : ℕ)
    (g : L ≃ₐ[k] L) (hg : g ∈ P.inertiaSubgroupIn k)
    (hrad : ∀ (α : L) (j : ℕ), α ^ (p ^ j) = (q : L) → g α = α) :
    ∃ w ∈ P.inertiaSubgroupIn k, w ^ (p ^ n) = g := by sorry
