-- Prove2me | Theorems.Thm_WeierstrassCurve_exists_isUnit_mul_pow_eight_eq_of_charTwo
-- name    : WeierstrassCurve.exists_isUnit_mul_pow_eight_eq_of_charTwo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.681435+00:00
-- url     : https://prove2.me/theorems/156fcf69-e70b-517e-ab9a-101e5c25a2db
-- title:
--   Order-3 points on y²+txy=x³+t⁵ force 8∣ v(t)
-- statement:
--   Let $M$ be a field of characteristic $2$ and let $A\subseteq M$ be a valuation subring. Let $t\in M$ be an element lying in $A$ which is not a unit of $A$ (i.e. $t$ belongs to the maximal ideal of $A$) and which is nonzero. Consider the Weierstrass curve over $M$ with coefficients $a_1=t$, $a_2=a_3=a_4=0$, $a_6=t^5$, that is the affine equation $y^2+t\,xy=x^3+t^5$, and let $x_0,y_0\in M$ be such that $(x_0,y_0)$ is a nonsingular point of this affine curve, so that it defines a point $P$ of the group of points of the curve. Assume that $3\cdot P=0$, i.e. $P$ is killed by $3$ in the group law, the zero element being the point at infinity. The conclusion is that there exist $\mu\in M$ and $u\in A$ such that $u$ is a unit of $A$ and $t=u\mu^8$ in $M$. Thus $t$ is a unit of $A$ times an eighth power; for $A$ a discrete valuation ring this says $8$ divides the valuation of $t$.
--
--   This is the wild part of the ramification of the $3$-division field of the curve $y^2+txy=x^3+t^5$ (a model with $j=t$) at $j=0$ in characteristic $2$: a rational point of order $3$ can only exist when the parameter $t$ is a unit times an eighth power. It is used in the construction of equivariant reductions of torsion on modular curves, in [`ModularCurve.exists_equivariant_torsion_reduction_ofJ`](thm.html#ModularCurve.exists_equivariant_torsion_reduction_ofJ), [`ModularCurve.exists_equivariant_torsion_reduction_ofJ_forall_place_reduceHom`](thm.html#ModularCurve.exists_equivariant_torsion_reduction_ofJ_forall_place_reduceHom) and [`ModularCurve.exists_frobeniusSemilinear_torsionModel_ofJ_univ`](thm.html#ModularCurve.exists_frobeniusSemilinear_torsionModel_ofJ_univ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_exists_isUnit_mul_pow_eight_eq_of_charTwo.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine

universe u in

theorem WeierstrassCurve.exists_isUnit_mul_pow_eight_eq_of_charTwo
    {M : Type u} [Field M] [CharP M 2] [DecidableEq M] (A : ValuationSubring M)
    {t : M} (ht : t ∈ A) (htu : ¬ IsUnit (⟨t, ht⟩ : A)) (ht0 : t ≠ 0)
    {x₀ y₀ : M} (hP : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.Nonsingular x₀ y₀)
    (h3P : (3 : ℕ) • Point.some x₀ y₀ hP = 0) :
    ∃ (μ : M) (u : A), IsUnit u ∧ t = u * μ ^ 8 := by sorry
