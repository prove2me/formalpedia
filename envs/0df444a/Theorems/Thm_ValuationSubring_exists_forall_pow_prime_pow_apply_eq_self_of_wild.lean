-- Prove2me | Theorems.Thm_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_self_of_wild
-- name    : ValuationSubring.exists_forall_pow_prime_pow_apply_eq_self_of_wild
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/a1f39218-63c4-5376-9826-77118366f5c9
-- title:
--   Wild elements act with q-power order at finite levels
-- statement:
--   Let $q$ be a prime number, let $P$ be a valuation subring of the algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$, and assume $P$ lies over $q$ in the sense that the image of $q$ in $\overline{\mathbb{Q}}$ belongs to `P.nonunits`, i.e. $q$ is a non-unit of $P$. Let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$ which is wild at $P$ in the elementwise sense that for every $z \in \overline{\mathbb{Q}}$ with $z \neq 0$ the element $\sigma(z)z^{-1} - 1$ is a non-unit of $P$. Let $F$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ which is finite-dimensional over $\mathbb{Q}$ and normal over $\mathbb{Q}$. Then there exists a natural number $a$ such that $\sigma^{q^{a}}(x) = x$ for every $x \in F$; equivalently, the restriction of $\sigma$ to $F$ has order a power of $q$ in $\mathrm{Gal}(F/\mathbb{Q})$. No hypothesis relating $\sigma$ to a decomposition or inertia subgroup at $P$ beyond the displayed wildness condition is imposed.
--
--   This is the elementwise form, at each finite normal level, of the statement that wild inertia at a place above $q$ is a $q$-group. It feeds the statements asserting that a wild element at $q$ acts trivially on an $\mathfrak{m}$-adically continuous lift whose residual representation is unramified at $q$, such as [`GaloisRepAdic.apply_eq_one_of_mem_inertiaSubgroupIn_of_wild`](thm.html#GaloisRepAdic.apply_eq_one_of_mem_inertiaSubgroupIn_of_wild) and [`GaloisRepAdic.apply_eq_one_of_wild_of_charpoly_eq`](thm.html#GaloisRepAdic.apply_eq_one_of_wild_of_charpoly_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_forall_pow_prime_pow_apply_eq_self_of_wild.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_forall_pow_prime_pow_apply_eq_self_of_wild {q : ℕ} (hq : q.Prime)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hwild : ∀ z : AlgebraicClosure ℚ, z ≠ 0 → σ z * z⁻¹ - 1 ∈ P.nonunits)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [Normal ℚ F] :
    ∃ a : ℕ, ∀ x ∈ F, (σ ^ (q ^ a)) x = x := by sorry
