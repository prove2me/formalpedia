-- Prove2me | Theorems.Thm_Polynomial_log_abv_eval_eq_log_gaussNorm_add_sum
-- name    : Polynomial.log_abv_eval_eq_log_gaussNorm_add_sum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/5b48bd38-60c6-5eab-9cbf-7dfccf26426d
-- title:
--   Non-archimedean Jensen formula on the closed unit disc
-- statement:
--   Let $K$ be an algebraically closed field and $v : K \to \mathbb{R}$ an absolute value on $K$ which is non-archimedean, i.e. satisfies the ultrametric inequality. Let $p \in K[X]$ be a nonzero polynomial and let $z \in K$ satisfy $v(z) \le 1$ and $p(z) \neq 0$. Then
--   $$\log v(p(z)) \;=\; \log \big(\|p\|_{v,1}\big) \;+\; \sum_{a} \log v(z-a),$$
--   where $\|p\|_{v,1}$ denotes the Gauss norm `p.gaussNorm v 1` of $p$ at radius $1$, that is $\max_k v(p_k)\cdot 1^k = \max_k v(p_k)$ over the coefficients $p_k$ of $p$, and where the sum is taken over the multiset obtained from the root multiset `p.roots` of $p$ in $K$ (roots counted with multiplicity) by keeping exactly those roots $a$ with $v(a) \le 1$, each contributing the term $\log v(z-a)$. Thus the equality is an identity of real numbers, valid at every point $z$ of the closed unit disc at which $p$ does not vanish, with no averaging over a circle.
--
--   This is the non-archimedean analogue of Jensen's formula for polynomials: on a non-archimedean algebraically closed field the value $v(p(z))$ at any point of the closed unit disc is computed exactly by the Gauss norm of $p$ together with the roots lying in the disc. It is used in the proof of [`Polynomial.exists_mem_roots_gaussNorm_mul_abv_sub_pow_le`](thm.html#Polynomial.exists_mem_roots_gaussNorm_mul_abv_sub_pow_le), which extracts from it a root near which $|p|$ is small relative to the Gauss norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_log_abv_eval_eq_log_gaussNorm_add_sum.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem Polynomial.log_abv_eval_eq_log_gaussNorm_add_sum {K : Type*} [Field K] [IsAlgClosed K]
    (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v) (p : K[X]) (hp : p ≠ 0)
    {z : K} (hz : v z ≤ 1) (hpz : p.eval z ≠ 0) :
    Real.log (v (p.eval z)) = Real.log (p.gaussNorm v 1)
      + ((p.roots.filter fun a => v a ≤ 1).map fun a => Real.log (v (z - a))).sum := by sorry
