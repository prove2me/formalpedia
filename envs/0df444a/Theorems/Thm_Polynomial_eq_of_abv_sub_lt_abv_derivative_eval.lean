-- Prove2me | Theorems.Thm_Polynomial_eq_of_abv_sub_lt_abv_derivative_eval
-- name    : Polynomial.eq_of_abv_sub_lt_abv_derivative_eval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/0d17a6f9-fa86-5773-acf7-bb54a8a7202a
-- title:
--   Uniqueness of roots within μ(g'(a)) (non-archimedean)
-- statement:
--   Let $K$ be a field and let $\mu$ be a real-valued absolute value on $K$ which is non-archimedean, in the sense that $\mu(x+y)\le\max(\mu x,\mu y)$ for all $x,y$. Let $g\in K[X]$ be a polynomial all of whose coefficients satisfy $\mu(g_i)\le 1$, and let $a,b\in K$ satisfy $\mu(a)\le 1$ and $\mu(b)\le 1$. Assume $a$ and $b$ are both roots of $g$, i.e. $g(a)=0$ and $g(b)=0$, and assume the strict inequality $\mu(a-b)<\mu\bigl(g'(a)\bigr)$, where $g'$ denotes the formal derivative of $g$. Then $a=b$. Note that the coefficient bound is imposed for every index $i$, so in particular $g$ is required to have $\mu$-integral coefficients in the strongest sense, and no completeness, discreteness or residue-characteristic hypothesis on $(K,\mu)$ is made; the hypothesis is vacuous when $g'(a)=0$.
--
--   This is the uniqueness half of Hensel's lemma in quantitative form: an integral root of an integral polynomial is the only integral root in the open ball of radius $\mu(g'(a))$ about itself. It is used in the construction of local charts on modular curves, where a root produced by a Newton-type approximation must be identified with a known nearby root; here it is cited by [`ModularCurve.JZero.exists_chart_of_isPivot`](thm.html#ModularCurve.JZero.exists_chart_of_isPivot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_eq_of_abv_sub_lt_abv_derivative_eval.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem Polynomial.eq_of_abv_sub_lt_abv_derivative_eval
    {K : Type*} [Field K] (μ : AbsoluteValue K ℝ) (hμ : IsNonarchimedean μ)
    (g : Polynomial K) (hg : ∀ i, μ (g.coeff i) ≤ 1) {a b : K} (ha : μ a ≤ 1) (hb : μ b ≤ 1)
    (hga : g.eval a = 0) (hgb : g.eval b = 0)
    (hlt : μ (a - b) < μ ((Polynomial.derivative g).eval a)) : a = b := by sorry
