-- Prove2me | Theorems.Thm_ValuationSubring_exists_dvd_pow_of_mem_maximalIdeal
-- name    : ValuationSubring.exists_dvd_pow_of_mem_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/b783e8e4-9b21-5727-8b99-88675a9bca7c
-- title:
--   Rank one: every nonzero element divides a power of a nonunit
-- statement:
--   Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ (the algebraic closure of $\mathbb{Q}$ as constructed in Mathlib), and let $q$ be a prime number. Assume that the image of $q$ in $\overline{\mathbb{Q}}$ lies in `A.nonunits`, that is, its valuation with respect to $A$ is strictly less than $1$; equivalently, $q$ lies in $A$ but is not invertible in $A$. Let $c$ be a nonzero element of $A$, and let $c'$ be a nonzero element of the maximal ideal of $A$ (the valuation subring $A$ being a local ring). Then there exists a natural number $M$ such that $c$ divides $c'^{\,M}$ in $A$. No bound on $M$ in terms of $c$, $c'$ or $q$ is asserted, only its existence.
--
--   This is the rank-one property of valuation rings of $\overline{\mathbb{Q}}$ whose maximal ideal contains a prime number: the value group is archimedean, so the $c'$-adic filtration is cofinal among principal ideals. It is used in the geometric part of the argument, where an arbitrary nonzero constant must be dominated by a power of a fixed nonunit, for instance in the construction and descent of semistable models of modular curves and in computations of orders of vanishing on curves over such valuation rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_dvd_pow_of_mem_maximalIdeal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_dvd_pow_of_mem_maximalIdeal
    (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} [Fact q.Prime]
    (hq : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A.nonunits)
    (c : A) (hc : c ≠ 0) (c' : A) (hc' : c' ∈ IsLocalRing.maximalIdeal A) (hc'0 : c' ≠ 0) :
    ∃ M : ℕ, c ∣ c' ^ M := by sorry
