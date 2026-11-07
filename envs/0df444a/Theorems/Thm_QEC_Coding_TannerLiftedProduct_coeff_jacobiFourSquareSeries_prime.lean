-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_prime
-- name    : QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_prime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T21:35:39.580352+00:00
-- url     : https://prove2.me/theorems/5e09b4ad-96b6-4771-ac4d-42a8638d903a
-- title:
--   Tanner Lifted Product: coeff jacobi Four Square Series prime
-- statement:
--   At a prime congruent to one modulo four, Jacobi's divisor sum has only
--   the divisors `1` and `p`, and hence equals `8 (p + 1)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FourSquareTheta.lean#L242-L252
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/FourSquareTheta.lean#L242-L252

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_FourSquareTheta
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset

theorem QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_prime
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    PowerSeries.coeff p jacobiFourSquareSeries = 8 * (p + 1) := by sorry
