-- Prove2me | Theorems.Thm_Polynomial_existsUnique_constantCoeff_eq_and_evalEval_C_add_X_eq_zero
-- name    : Polynomial.existsUnique_constantCoeff_eq_and_evalEval_C_add_X_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/1ef558e7-db75-5476-b3be-eed690c1196d
-- title:
--   Formal branch through a simple point of a plane curve
-- statement:
--   Let $K$ be a field and let $G$ be a polynomial in one variable over $K[Z]$, i.e. $G \in K[Z][Y]$, and let $z_0, y_0 \in K$. Here `evalEval z₀ y₀` means substituting $y_0$ for the outer variable and $z_0$ for the inner one, so the two hypotheses read $G(z_0,y_0) = 0$ and $(\partial G/\partial Y)(z_0,y_0) \neq 0$, the derivative being the formal derivative of $G$ as a polynomial in the outer variable $Y$ over $K[Z]$. The conclusion asserts that there is exactly one power series $Y \in K[[T]]$ such that the constant coefficient of $Y$ equals $y_0$ and $G(z_0 + T, Y) = 0$ in $K[[T]]$; the substitution is spelled as follows: the coefficients of $G$ are pushed into $K[[T]]$ by the structure map $K \to K[[T]]$ applied coefficientwise to the inner polynomials, the inner variable is evaluated at $\mathrm{C}(z_0) + X$ and the outer variable at $Y$, and the resulting element of $K[[T]]$ is required to vanish.
--
--   This is the formal implicit function theorem over an arbitrary field: the unique formal branch $Y(T)$ of the plane curve $G = 0$ through a point that is simple in the $Y$-direction, with the base parameter $T = Z - z_0$. It is used in the construction of local charts on the modular curve, via [`ModularCurve.JZero.exists_chart_of_isPivot`](thm.html#ModularCurve.JZero.exists_chart_of_isPivot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Polynomial_existsUnique_constantCoeff_eq_and_evalEval_C_add_X_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem Polynomial.existsUnique_constantCoeff_eq_and_evalEval_C_add_X_eq_zero
    {K : Type*} [Field K] (G : Polynomial (Polynomial K)) (z₀ y₀ : K)
    (h0 : G.evalEval z₀ y₀ = 0) (hsep : (Polynomial.derivative G).evalEval z₀ y₀ ≠ 0) :
    ∃! Y : PowerSeries K, PowerSeries.constantCoeff Y = y₀ ∧
      (G.map (Polynomial.mapRingHom (algebraMap K (PowerSeries K)))).evalEval
        (PowerSeries.C z₀ + PowerSeries.X) Y = 0 := by sorry
