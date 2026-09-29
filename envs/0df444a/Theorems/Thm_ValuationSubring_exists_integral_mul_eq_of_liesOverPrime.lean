-- Prove2me | Theorems.Thm_ValuationSubring_exists_integral_mul_eq_of_liesOverPrime
-- name    : ValuationSubring.exists_integral_mul_eq_of_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.105901+00:00
-- url     : https://prove2.me/theorems/b0fedae7-61b2-5fbf-ab59-895be943e689
-- title:
--   Every place of ℚ̄ above q localises ℤ̄
-- statement:
--   Let $A$ be a valuation subring of the algebraic closure $\bar{\mathbb Q}$ of $\mathbb Q$, let $q$ be a prime natural number, and assume that $A$ lies over $q$ in the sense that the image of $q$ in $\bar{\mathbb Q}$ belongs to `A.nonunits`, the set of non-units of $A$ (that is, $q$ lies in the maximal ideal of $A$). Let $a$ be an element of $\bar{\mathbb Q}$ lying in $A$. Then there exist two elements $x$ and $s$ of the integral closure $\bar{\mathbb Z}$ of $\mathbb Z$ in $\bar{\mathbb Q}$ such that $s$, viewed in $\bar{\mathbb Q}$, is not in `A.nonunits` — i.e. $s$ is a unit of $A$ — and $a \cdot s = x$ holds in $\bar{\mathbb Q}$ (the product being taken after mapping $s$ and $x$ into $\bar{\mathbb Q}$). Thus every element of $A$ can be written as a quotient of an algebraic integer by an algebraic integer that is a unit of $A$; equivalently, $A$ is the localisation of $\bar{\mathbb Z}$ at the prime $\bar{\mathbb Z} \cap \mathfrak m_A$.
--
--   This is the standard dictionary identifying valuation subrings of $\bar{\mathbb Q}$ with localisations of the ring $\bar{\mathbb Z}$ of algebraic integers at its maximal ideals, in the form needed when places are assumed to lie over a fixed prime $q$. It is used in the comparison of valuation-theoretic and ideal-theoretic descriptions of places, for instance in the analysis of specialisations of places on modular curves and in transporting places by Galois automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_integral_mul_eq_of_liesOverPrime.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.exists_integral_mul_eq_of_liesOverPrime (A : ValuationSubring (AlgebraicClosure ℚ)) {q : ℕ} (hq : q.Prime) (hA : A.LiesOverPrime q) (a : AlgebraicClosure ℚ) (ha : a ∈ A) : ∃ x s : integralClosure ℤ (AlgebraicClosure ℚ), (s : AlgebraicClosure ℚ) ∉ A.nonunits ∧ a * s = x := by sorry
