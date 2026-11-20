-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaSquareMean_hasSum
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaSquareMean_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:32:09.350052+00:00
-- url     : https://prove2.me/theorems/e42b3829-6a61-4b51-a65e-5d5a2b30e385
-- title:
--   Tanner Lifted Product: lps Theta Square Mean has Sum
-- statement:
--   The actual LPS square mean has the genuine exponentially weighted coefficient-square expansion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaSquareMean.lean#L50-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaSquareMean.lean#L50-L54

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaSquareMean
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaSquareMean_hasSum (q : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (y : ℝ) (hy : 0<y) :
    HasSum (fun n : ℕ => (lpsThetaSquareCoeff q hq4 n:ℂ)*
      (Real.exp (-(4*Real.pi*(n:ℝ))*y):ℂ)) (lpsThetaSquareMean q hq4 y:ℂ) := by sorry
