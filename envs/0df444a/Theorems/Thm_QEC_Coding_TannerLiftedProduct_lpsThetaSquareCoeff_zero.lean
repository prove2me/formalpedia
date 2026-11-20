-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaSquareCoeff_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaSquareCoeff_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:31:08.59346+00:00
-- url     : https://prove2.me/theorems/a1ad7937-e645-494f-8195-5499dd32aad1
-- title:
--   Tanner Lifted Product: lps Theta Square Coeff zero
-- statement:
--   The actual LPS remainder has zero constant square coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaSquareMean.lean#L30-L32
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaSquareMean.lean#L30-L32

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaSquareMean
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaSquareCoeff_zero (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) :
    lpsThetaSquareCoeff q hq4 0=0 := by sorry
