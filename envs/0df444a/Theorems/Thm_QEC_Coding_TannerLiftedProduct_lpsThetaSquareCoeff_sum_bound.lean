-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaSquareCoeff_sum_bound
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaSquareCoeff_sum_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:31:43.096077+00:00
-- url     : https://prove2.me/theorems/2dde8963-608d-4bd7-8538-bb2c2dc2bf3a
-- title:
--   Tanner Lifted Product: lps Theta Square Coeff sum bound
-- statement:
--   The actual LPS coefficient squares satisfy the proved initial quadratic average estimate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaSquareMean.lean#L57-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaSquareMean.lean#L57-L61

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaSquareMean
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaSquareCoeff_sum_bound (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    ∃ C : ℝ, 0≤C ∧ ∀ X : ℕ,
      (∑ n ∈ Finset.range X, lpsThetaSquareCoeff q hq4 n)≤C*(X:ℝ)^2 := by sorry
