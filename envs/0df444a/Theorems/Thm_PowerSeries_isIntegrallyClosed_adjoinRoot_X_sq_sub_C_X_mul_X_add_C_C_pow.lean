-- Prove2me | Theorems.Thm_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow
-- name    : PowerSeries.isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/5241f6fb-3737-5848-ba52-f3e87fd1b24a
-- title:
--   Normality of D[[s][X]/(X²-sX+varpi^e)
-- statement:
--   Let $D$ be a commutative ring which is a domain and a discrete valuation ring, let $\varpi \in D$ be an irreducible element, and let $e$ be a natural number with $1 \le e$. Consider the power series ring $D[\![s]\![$ (with $s$ denoting the power series variable `PowerSeries.X`) and, inside the polynomial ring $D[\![s]\![[X]$, the quadratic polynomial
--   $$X^2 - s\,X + \varpi^e,$$
--   where the linear coefficient is the constant polynomial with value the power series variable and the constant coefficient is the constant polynomial with value the constant power series $\varpi^e$. The assertion is that the quotient ring obtained by adjoining a root of this polynomial, i.e. $D[\![s]\![[X]/(X^2 - sX + \varpi^e)$ as produced by `AdjoinRoot`, is integrally closed: it satisfies Mathlib's `IsIntegrallyClosed`, so every element of its fraction field that is integral over it already lies in (the image of) the ring.
--
--   This is the normality of the $A_{e-1}$ surface singularity $uv = \varpi^e$ over a discrete valuation ring, written in the symmetric coordinate $s = u+v$, so that $u$ satisfies $X^2 - sX + \varpi^e$; for $e = 1$ the ring is even regular, while for $e \ge 2$ it is normal but singular. It serves as the integral-closedness input for the local models of the crossing of two components on a modular curve, and is used by [`ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow`](thm.html#ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow) and [`ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete`](thm.html#ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem PowerSeries.isIntegrallyClosed_adjoinRoot_X_sq_sub_C_X_mul_X_add_C_C_pow
    {D : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    (ϖ : D) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) :
    IsIntegrallyClosed (AdjoinRoot (Polynomial.X ^ 2 -
      Polynomial.C (PowerSeries.X : PowerSeries D) * Polynomial.X +
      Polynomial.C (PowerSeries.C (ϖ ^ e)) : Polynomial (PowerSeries D))) := by sorry
