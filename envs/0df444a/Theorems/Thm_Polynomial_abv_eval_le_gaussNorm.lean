-- Prove2me | Theorems.Thm_Polynomial_abv_eval_le_gaussNorm
-- name    : Polynomial.abv_eval_le_gaussNorm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/889c1403-62ca-575d-aa53-71f384a93c63
-- title:
--   Polynomials are bounded by their Gauss norm on a disc
-- statement:
--   Let $R$ be a commutative ring, let $v \colon R \to \mathbb{R}$ be an absolute value on $R$, and assume $v$ is non-archimedean, i.e. $v(x+y) \le \max(v(x), v(y))$ for all $x, y \in R$. Let $c$ be a real number with $0 \le c$, let $p \in R[X]$, and let $z \in R$ satisfy $v(z) \le c$. The assertion is that $v(p(z)) \le \lVert p \rVert_{v,c}$, where $\lVert p \rVert_{v,c}$ denotes `Polynomial.gaussNorm v c p`, the Gauss norm of $p$ at radius $c$, namely the supremum of the quantities $v(p_i)\,c^i$ over the coefficients $p_i$ of $p$ (equal to $0$ for $p = 0$). Thus a polynomial evaluated anywhere on the closed disc of radius $c$ about $0$ is bounded in absolute value by its Gauss norm for that radius; no hypothesis on $R$ beyond commutativity is imposed.
--
--   This is the elementary half of the maximum modulus principle for polynomials over a non-archimedean absolute value: the Gauss norm dominates the sup norm on the closed disc of the corresponding radius. It is used in the estimate [`Polynomial.exists_mem_roots_gaussNorm_mul_abv_sub_pow_le_of_evalEval_eq_zero`](thm.html#Polynomial.exists_mem_roots_gaussNorm_mul_abv_sub_pow_le_of_evalEval_eq_zero), which locates a root of a polynomial close to a given approximate zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_abv_eval_le_gaussNorm.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem Polynomial.abv_eval_le_gaussNorm {R : Type*} [CommRing R] (v : AbsoluteValue R ℝ)
    (hv : IsNonarchimedean v) {c : ℝ} (hc : 0 ≤ c) (p : R[X]) {z : R} (hz : v z ≤ c) :
    v (p.eval z) ≤ p.gaussNorm v c := by sorry
