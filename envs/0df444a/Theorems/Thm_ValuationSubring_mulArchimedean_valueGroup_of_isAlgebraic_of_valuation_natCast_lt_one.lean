-- Prove2me | Theorems.Thm_ValuationSubring_mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one
-- name    : ValuationSubring.mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/51635905-18e1-5c11-a7e1-4560bdd00206
-- title:
--   Value group of a place above p in ℚ̄ is archimedean
-- statement:
--   Let $K$ be a field equipped with a $\mathbb{Q}$-algebra structure such that $K$ is algebraic over $\mathbb{Q}$, and let $A$ be a valuation subring of $K$, with associated valuation $A.\mathrm{valuation}$ taking values in the linearly ordered commutative group with zero $A.\mathrm{ValueGroup}$. Let $p$ be a prime number, viewed in $K$ through the canonical map $\mathbb{N} \to K$, and assume that $A.\mathrm{valuation}(p) < 1$, i.e. that the place determined by $A$ lies above $p$. The conclusion is that $A.\mathrm{ValueGroup}$ is multiplicatively archimedean in Mathlib's sense: for all elements $x, y$ of the value group with $1 < y$ there exists a natural number $n$ with $x \le y^{n}$. Equivalently, the valuation has rank one, no proper convex subgroup separating $1$ from the value of $p$ being available.
--
--   This is the standard fact that a valuation of an algebraic extension of $\mathbb{Q}$ whose residue characteristic is positive has rank one, so that its value group admits an order embedding into the positive reals and $K$ becomes a non-archimedean normed field with unit ball $A$. It is used, via the archimedean property, in the rigid-analytic and formal-geometric arguments on modular curves and on Picard groups of curves that appear later in the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ValuationSubring.mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one
    {K : Type*} [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (A : ValuationSubring K) {p : ℕ} (hp : p.Prime) (hAp : A.valuation (p : K) < 1) :
    MulArchimedean A.ValueGroup := by sorry
