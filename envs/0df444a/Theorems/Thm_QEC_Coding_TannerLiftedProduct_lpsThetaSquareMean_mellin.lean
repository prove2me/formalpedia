-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaSquareMean_mellin
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaSquareMean_mellin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:33:13.569388+00:00
-- url     : https://prove2.me/theorems/f7bd6069-3436-4601-81c3-665bc20ff807
-- title:
--   Tanner Lifted Product: lps Theta Square Mean mellin
-- statement:
--   The genuine LPS square mean has its exact Gamma-over-four-pi Mellin representation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaSquareMean.lean#L71-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaSquareMean.lean#L71-L77

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaSquareMean
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaSquareMean_mellin (q : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (s : ℂ) (hs : 2<s.re) :
    mellin (fun y : ℝ => (lpsThetaSquareMean q hq4 y:ℂ)) s=
      (Complex.Gamma s/((4*Real.pi:ℝ):ℂ)^s)*
        LSeries (fun n : ℕ => (lpsThetaSquareCoeff q hq4 n:ℂ)) s := by sorry
