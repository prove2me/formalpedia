-- Prove2me | Theorems.Thm_Transcendental_exists_irreducible_evalEval_eq_zero_and_derivative_ne_zero
-- name    : Transcendental.exists_irreducible_evalEval_eq_zero_and_derivative_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/c7c0113c-79f0-5769-ad86-bc583b53d012
-- title:
--   Separable plane relation between two function field elements
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and assume $K$ has characteristic $0$. Let $x_0 \in F$ be an element such that $F$ is finite-dimensional as a vector space over the intermediate field $K(x_0)$ obtained by adjoining $x_0$ to $K$ inside $F$; thus $F$ is a finite extension of $K(x_0)$. Let $z \in F$ be transcendental over $K$, and let $y \in F$ be arbitrary. The conclusion asserts the existence of a polynomial $G$ in two variables, presented as an element of $K[Z][Y]$, which is irreducible in that ring and satisfies the following two conditions after its coefficients are pushed forward along the structure map $K \to F$ (coefficientwise in both variables): evaluating the inner variable $Z$ at $z$ and then the outer variable $Y$ at $y$ gives $G(z,y) = 0$ in $F$, while performing the same two evaluations on the derivative of $G$ with respect to the outer variable $Y$ gives $(\partial G/\partial Y)(z,y) \neq 0$ in $F$. So $y$ satisfies an irreducible plane relation over $K$ with $z$, and that relation is separable in $y$ at the point $(z,y)$.
--
--   This is the standard algebraic input from the theory of algebraic function fields of one variable in characteristic $0$: any two elements of such a field are linked by an irreducible plane relation which may be taken separable in the second variable. It is used in the construction of local charts on modular curves, where the non-vanishing of $\partial G/\partial Y$ at the generic point $(z,y)$ makes $y$ a Hensel root of $G(z,\cdot)$ at all but finitely many points; it is cited by the results on [`ModularCurve.JZero`](def/ModularCurve_ArithmeticGalois.html#L115) concerning orders of vanishing and evaluation of such relations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Transcendental_exists_irreducible_evalEval_eq_zero_and_derivative_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem Transcendental.exists_irreducible_evalEval_eq_zero_and_derivative_ne_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F] [CharZero K]
    (x₀ : F) [FiniteDimensional (IntermediateField.adjoin K ({x₀} : Set F)) F]
    {z : F} (hz : Transcendental K z) (y : F) :
    ∃ G : Polynomial (Polynomial K), Irreducible G ∧
      (G.map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y = 0 ∧
      ((Polynomial.derivative G).map (Polynomial.mapRingHom (algebraMap K F))).evalEval z y ≠ 0 := by sorry
