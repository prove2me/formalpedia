-- Prove2me | Theorems.Thm_Polynomial_valuation_root_dichotomy_of_kroneckerShape
-- name    : Polynomial.valuation_root_dichotomy_of_kroneckerShape
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/bbc4f1ef-0967-5646-9f30-d49331b312af
-- title:
--   Root-size dichotomy for Kronecker-shaped polynomials over a valued field
-- statement:
--   Let $K$ be a field equipped with a valuation $v$ taking values, written multiplicatively, in a linearly ordered commutative group with zero $\Gamma_0$. Let $q$ be a natural number with $q > 1$, let $x_0, c \in K$ satisfy $v(x_0) > 1$ and $v(c) \le 1$, and let $H \in K[X]$ be a polynomial whose natural degree is at most $q$ and whose coefficients obey $v(H_b) \le v(x_0)^q$ for every $b < q$ and $v(H_q) \le v(x_0)^{q-1}$. Suppose $y \in K$ is a root of the polynomial $$\bigl(C(x_0^q) - X\bigr)\bigl(C(x_0) - X^q\bigr) + C(c)\,H,$$ that is, its evaluation at $y$ vanishes. Then one of the following two alternatives holds: either $v(y) = v(x_0)^q$ and $v(y - x_0^q) \le v(c)\,v(x_0)^{q-1}$, or $v(y)^q = v(x_0)$ and $v(x_0 - y^q) \le v(c)\,v(y)^{q-1}$. Here $q - 1$ is truncated subtraction of natural numbers, harmless since $q > 1$.
--
--   An ultrametric root-location estimate: a root of a perturbed product $(x_0^q - Y)(x_0 - Y^q)$ must sit, in valuation, at one of the two unperturbed sizes $v(x_0)^q$ or $v(x_0)^{1/q}$, and be correspondingly close to the relevant unperturbed root. It is used by [`Polynomial.roots_filter_valuation_eq_singleton_of_kroneckerShape`](thm.html#Polynomial.roots_filter_valuation_eq_singleton_of_kroneckerShape) and [`Polynomial.valuation_div_sub_one_lt_one_of_kroneckerShape`](thm.html#Polynomial.valuation_div_sub_one_lt_one_of_kroneckerShape).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_valuation_root_dichotomy_of_kroneckerShape.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem Polynomial.valuation_root_dichotomy_of_kroneckerShape
    {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
    {q : ℕ} (hq : 1 < q) (x₀ c : K) (hx : 1 < v x₀) (hc : v c ≤ 1)
    (H : K[X]) (hHdeg : H.natDegree ≤ q)
    (hHb : ∀ b < q, v (H.coeff b) ≤ v x₀ ^ q) (hHq : v (H.coeff q) ≤ v x₀ ^ (q - 1))
    (y : K) (hy : ((C (x₀ ^ q) - X) * (C x₀ - X ^ q) + C c * H).IsRoot y) :
    (v y = v x₀ ^ q ∧ v (y - x₀ ^ q) ≤ v c * v x₀ ^ (q - 1)) ∨
      (v y ^ q = v x₀ ∧ v (x₀ - y ^ q) ≤ v c * v y ^ (q - 1)) := by sorry
