-- Prove2me | Theorems.Thm_ValuationSubring_exists_valuation_pow_lt_of_isAlgebraic
-- name    : ValuationSubring.exists_valuation_pow_lt_of_isAlgebraic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/fee844ce-c0c7-53f0-8047-b886cbada99c
-- title:
--   Powers of v(π₀) eventually below any nonzero value
-- statement:
--   Let $F$ be a field equipped with a $\mathbb{Q}$-algebra structure such that $F$ is algebraic over $\mathbb{Q}$, and let $O$ be a valuation subring of $F$, with associated valuation `O.valuation` taking values in the linearly ordered commutative group with zero `O.ValueGroup`. Let $\pi_0 \in F$ be an element whose value $v(\pi_0) :=$ `O.valuation π₀` is nonzero and satisfies $v(\pi_0) < 1$; equivalently, $\pi_0$ is a nonzero element of the maximal ideal of $O$. Let $\gamma$ be a nonzero element of `O.ValueGroup`. The assertion is that there exists a natural number $n$ with $v(\pi_0)^n < \gamma$. Thus no nonzero element of the value group is a lower bound for the powers of $v(\pi_0)$: the value group is archimedean with respect to $v(\pi_0)$, and the powers of $v(\pi_0)$ are cofinal downwards among the nonzero values.
--
--   This is the archimedean (commensurability) property of the value group of a valuation on a field algebraic over $\mathbb{Q}$, relative to a fixed element of value strictly between $0$ and $1$; it expresses that the valuation topology is the $\pi_0$-adic one. It is used in the treatment of places and their prolongations on modular curves, for instance by [`ModularCurve.DRModelPackageLevel.extendsToPlace_pts_of_isGoodClass`](thm.html#ModularCurve.DRModelPackageLevel.extendsToPlace_pts_of_isGoodClass) and by the bounds on prolongation tuples in [`ModularCurve.PlaceSpecialization`](def/ModularCurve_PlaceSpecialization.html#L13).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_exists_valuation_pow_lt_of_isAlgebraic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.exists_valuation_pow_lt_of_isAlgebraic
    {F : Type*} [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F] (O : ValuationSubring F)
    {π₀ : F} (h0 : O.valuation π₀ ≠ 0) (h1 : O.valuation π₀ < 1) (γ : O.ValueGroup) (hγ : γ ≠ 0) :
    ∃ n : ℕ, O.valuation π₀ ^ n < γ := by sorry
