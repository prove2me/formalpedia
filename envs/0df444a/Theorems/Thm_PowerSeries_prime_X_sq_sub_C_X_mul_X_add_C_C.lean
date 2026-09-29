-- Prove2me | Theorems.Thm_PowerSeries_prime_X_sq_sub_C_X_mul_X_add_C_C
-- name    : PowerSeries.prime_X_sq_sub_C_X_mul_X_add_C_C
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/f576239a-25d2-518b-936f-c40b6155c5de
-- title:
--   Primality of X² - sX + c over D[[s]]
-- statement:
--   Let $D$ be a commutative ring which is a domain and a principal ideal ring, and let $c \in D$ satisfy $c \neq 0$ and $c$ is not a unit. Form the ring of formal power series $D[\![s]\!]$ in one variable over $D$, and inside the polynomial ring $D[\![s]\!][X]$ consider the monic quadratic $$X^2 - \mathrm{C}(s)\,X + \mathrm{C}(c),$$ where $\mathrm{C}$ denotes the inclusion of coefficients $D[\![s]\!] \to D[\![s]\!][X]$, the linear coefficient is the power-series variable $s$ and the constant coefficient is the image of $c$ under the constant-coefficient inclusion $D \to D[\![s]\!]$. The assertion is that this polynomial is a prime element of $D[\![s]\!][X]$: it is non-zero, not a unit, and whenever it divides a product it divides one of the factors. Equivalently, the quotient $D[\![s]\!][X]/(X^2 - sX + c)$ is an integral domain.
--
--   An elementary commutative-algebra input, proved by way of irreducibility together with Gauss's lemma over a unique factorisation domain. It is used in the study of the crossing local model $W[\![u,v]\!]/(uv - \varpi^e)$ over a discrete valuation ring, where it feeds the integral-closedness statements [`ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow`](thm.html#ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow) and [`ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete`](thm.html#ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PowerSeries_prime_X_sq_sub_C_X_mul_X_add_C_C.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem PowerSeries.prime_X_sq_sub_C_X_mul_X_add_C_C
    {D : Type*} [CommRing D] [IsDomain D] [IsPrincipalIdealRing D]
    {c : D} (hc0 : c ≠ 0) (hcu : ¬IsUnit c) :
    Prime (Polynomial.X ^ 2 - Polynomial.C (PowerSeries.X : PowerSeries D) * Polynomial.X +
      Polynomial.C (PowerSeries.C c) : Polynomial (PowerSeries D)) := by sorry
