-- Prove2me | Theorems.Thm_Valuation_map_eval_eq_pow_of_one_lt
-- name    : Valuation.map_eval_eq_pow_of_one_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/1c45b520-afd4-5c36-90b5-dd26b8d8c1d2
-- title:
--   Dominant leading term of a valuation at a pole
-- statement:
--   Let $R$ be a commutative ring, let $\Gamma_0$ be a linearly ordered commutative group with zero, and let $v \colon R \to \Gamma_0$ be a valuation. Let $f \in R[X]$ and $x \in R$ be such that: every coefficient of $f$ satisfies $v(f_i) \le 1$; the leading coefficient of $f$ has $v(\mathrm{lc}(f)) = 1$ (which in particular forces $f \ne 0$, since $v(0) = 0$); and $x$ is a pole for $v$ in the sense that $1 < v(x)$. Then the value of $v$ at $f(x)$, the evaluation of $f$ at $x$, is exactly $v(x)^{d}$, where $d = \deg f$ is the natural-number degree of $f$. Since $v(x) > 1 > 0$, the conclusion gives $v(f(x)) \ne 0$, so $f(x) \ne 0$ whenever $v$ has trivial support at $f(x)$; the statement itself is the equality of valuations, not the non-vanishing.
--
--   This is the standard non-archimedean estimate that at a pole the leading term of a polynomial with $v$-integral coefficients and $v$-unit leading coefficient strictly dominates all lower terms. It is used to show that torsion points of order prime to the residue characteristic have integral coordinates, via application to a division polynomial whose leading coefficient is a unit; in this development it is cited by [`WeierstrassCurve.torsion_integral_of_not_dvd`](thm.html#WeierstrassCurve.torsion_integral_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Valuation_map_eval_eq_pow_of_one_lt.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Valuation.map_eval_eq_pow_of_one_lt {R : Type*} [CommRing R]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)
    {f : Polynomial R} {x : R} (hc : ∀ i, v (f.coeff i) ≤ 1) (hl : v f.leadingCoeff = 1)
    (hx : 1 < v x) : v (f.eval x) = v x ^ f.natDegree := by sorry
