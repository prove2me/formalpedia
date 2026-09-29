-- Prove2me | Theorems.Thm_Polynomial_exists_mem_roots_gaussNorm_mul_abv_sub_pow_le
-- name    : Polynomial.exists_mem_roots_gaussNorm_mul_abv_sub_pow_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/b84aaac4-3222-5fe5-9a18-b294335cbc09
-- title:
--   Nearest root on the non-archimedean closed unit disc
-- statement:
--   Let $K$ be an algebraically closed field and let $v : K \to \mathbb{R}$ be an absolute value on $K$ that is non-archimedean, i.e. satisfies $v(x+y) \le \max(v(x), v(y))$. Let $p \in K[X]$ be a polynomial, and write $\lVert p \rVert_1$ for its Gauss norm of radius $1$, `p.gaussNorm v 1`, the supremum of $v$ on the coefficients of $p$. Let $z \in K$ satisfy $v(z) \le 1$, and assume that the value of $p$ at $z$ is strictly smaller than the Gauss norm, $v(p(z)) < \lVert p \rVert_1$. The conclusion asserts the existence of an element $a$ belonging to the root multiset `p.roots` of $p$ such that $v(a) \le 1$ and $$\lVert p \rVert_1 \cdot v(z - a)^{\deg p} \le v(p(z)),$$ the exponent being the natural-number degree `p.natDegree`. Note that the hypothesis $v(p(z)) < \lVert p \rVert_1$ forces $\lVert p \rVert_1 > 0$, hence $p \ne 0$, so that the root multiset is the expected one; membership in `p.roots` indeed means $p(a) = 0$.
--
--   This is a quantitative statement about the distance from a point of the closed unit disc to the zero set of a polynomial: at a point where $p$ is strictly smaller than its Gauss norm, some root in the closed unit disc lies within distance $(v(p(z))/\lVert p \rVert_1)^{1/\deg p}$ of $z$. It is used in the two-variable form [`Polynomial.exists_mem_roots_gaussNorm_mul_abv_sub_pow_le_of_evalEval_eq_zero`](thm.html#Polynomial.exists_mem_roots_gaussNorm_mul_abv_sub_pow_le_of_evalEval_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_exists_mem_roots_gaussNorm_mul_abv_sub_pow_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem Polynomial.exists_mem_roots_gaussNorm_mul_abv_sub_pow_le {K : Type*} [Field K]
    [IsAlgClosed K] (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) (p : K[X])
    {z : K} (hz : v z ≤ 1) (hlt : v (p.eval z) < p.gaussNorm v 1) :
    ∃ a ∈ p.roots, v a ≤ 1 ∧ p.gaussNorm v 1 * v (z - a) ^ p.natDegree ≤ v (p.eval z) := by sorry
