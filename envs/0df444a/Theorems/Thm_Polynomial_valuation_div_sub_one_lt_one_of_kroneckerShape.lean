-- Prove2me | Theorems.Thm_Polynomial_valuation_div_sub_one_lt_one_of_kroneckerShape
-- name    : Polynomial.valuation_div_sub_one_lt_one_of_kroneckerShape
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/c1c20d11-0562-5660-ae3a-f9c6b6fb02d2
-- title:
--   Kronecker-shape root estimate, quotient form
-- statement:
--   Let $K$ be a field, let $\Gamma_0$ be a linearly ordered commutative group with zero and let $v : K \to \Gamma_0$ be a valuation. Let $q$ be a natural number with $1 < q$, let $x_0, c \in K$ satisfy $1 < v(x_0)$ and $v(c) \le 1$, and let $H \in K[X]$ have $\deg H \le q$ with coefficient bounds $v(H_b) \le v(x_0)^q$ for every $b < q$ and $v(H_q) \le v(x_0)^{q-1}$. Let $y \in K$ be a root of the polynomial $$(x_0^q - X)\,(x_0 - X^q) + c\,H(X).$$ Then one of the following holds: either $v\bigl(y/x_0^q - 1\bigr) < 1$, or else both $1 < v(y)$ and $v\bigl(x_0/y^q - 1\bigr) < 1$. Thus every root of a polynomial of this shape is, multiplicatively, within the open unit ball of either $x_0^q$ or of a $q$-th root of $x_0$, the second alternative coming with the additional information that $y$ itself has valuation exceeding $1$.
--
--   This is the quotient (relative-distance) form of the ultrametric root estimate for polynomials of Kronecker shape $(x_0^q - X)(x_0 - X^q) + cH(X)$. It is used in the dichotomy [`ModularCurve.isInftySide_or_isZeroSide_of_isCuspidal`](thm.html#ModularCurve.isInftySide_or_isZeroSide_of_isCuspidal), which sorts cuspidal points into those near the $\infty$-side and those near the $0$-side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_valuation_div_sub_one_lt_one_of_kroneckerShape.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem Polynomial.valuation_div_sub_one_lt_one_of_kroneckerShape
    {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
    {q : ℕ} (hq : 1 < q) (x₀ c : K) (hx : 1 < v x₀) (hc : v c ≤ 1)
    (H : K[X]) (hHdeg : H.natDegree ≤ q)
    (hHb : ∀ b < q, v (H.coeff b) ≤ v x₀ ^ q) (hHq : v (H.coeff q) ≤ v x₀ ^ (q - 1))
    (y : K) (hy : ((C (x₀ ^ q) - X) * (C x₀ - X ^ q) + C c * H).IsRoot y) :
    v (y / x₀ ^ q - 1) < 1 ∨ (1 < v y ∧ v (x₀ / y ^ q - 1) < 1) := by sorry
