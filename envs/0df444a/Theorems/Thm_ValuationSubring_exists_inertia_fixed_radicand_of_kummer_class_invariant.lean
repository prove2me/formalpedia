-- Prove2me | Theorems.Thm_ValuationSubring_exists_inertia_fixed_radicand_of_kummer_class_invariant
-- name    : ValuationSubring.exists_inertia_fixed_radicand_of_kummer_class_invariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/374b53e3-bb9d-59b8-96a8-92f6cfc003ae
-- title:
--   Inertia-invariant Kummer class has an inertia-fixed radicand
-- statement:
--   Fix a prime $p \neq 2$ and natural numbers $n \le N$, and let $P$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` such that $p$, viewed in $\overline{\mathbb{Q}}$, is a nonunit of $P$ (the predicate `LiesOverPrime`), so that $P$ is a valuation subring over the rational prime $p$. Write $I$ for `P.inertiaSubgroupIn ℚ`, the image in $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$ under the inclusion of the decomposition subgroup, and write $J_N \subseteq I$ for the set of $\sigma \in I$ fixing every $\xi \in \overline{\mathbb{Q}}$ with $\xi^{p^N} = 1$. Let $x \in \overline{\mathbb{Q}}$ be nonzero and suppose (i) every $\sigma \in J_N$ fixes $x$, and (ii) for every $\sigma \in I$ there is $w \in \overline{\mathbb{Q}}$ fixed by every element of $J_N$ with $\sigma x = x \, w^{p^n}$; that is, the class of $x$ modulo $p^n$-th powers of $J_N$-fixed elements is $I$-invariant. The conclusion asserts the existence of $x', w' \in \overline{\mathbb{Q}}$ with $x' \neq 0$, with $\sigma x' = x'$ for every $\sigma \in I$, with $\tau w' = w'$ for every $\tau \in J_N$, and with $x = x' \, w'^{p^n}$.
--
--   This is the descent step for Kummer classes at a prime above $p$: an element of the $p^N$-th cyclotomic layer over the inertia-fixed field whose class modulo $p^n$-th powers is invariant under inertia already comes from an inertia-fixed element, the failure at $p = 2$ being exhibited by $-4 = (1+i)^4$. The proof uses only the description of the action of inertia on $p^k$-th roots of unity through $(\mathbb{Z}/p^k)^\times$ given by [`ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one`](thm.html#ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow_of_pow_prime_pow_eq_one), and the result feeds into [`ValuationSubring.exists_inertia_fixed_kummer_generator_of_additive_character`](thm.html#ValuationSubring.exists_inertia_fixed_kummer_generator_of_additive_character).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_inertia_fixed_radicand_of_kummer_class_invariant.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_inertia_fixed_radicand_of_kummer_class_invariant
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (N n : ℕ) (hn : n ≤ N)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (x : AlgebraicClosure ℚ) (hx0 : x ≠ 0)
    (hxfix : ∀ σ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → σ ξ = ξ) → σ x = x)
    (hinv : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∃ w : AlgebraicClosure ℚ,
      (∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) → τ w = w) ∧ σ x = x * w ^ p ^ n) :
    ∃ x' w' : AlgebraicClosure ℚ, x' ≠ 0 ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, σ x' = x') ∧
      (∀ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ξ : AlgebraicClosure ℚ, ξ ^ p ^ N = 1 → τ ξ = ξ) → τ w' = w') ∧
      x = x' * w' ^ p ^ n := by sorry
