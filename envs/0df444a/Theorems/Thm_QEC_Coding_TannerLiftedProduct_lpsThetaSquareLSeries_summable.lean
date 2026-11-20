-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaSquareLSeries_summable
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaSquareLSeries_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:31:23.426449+00:00
-- url     : https://prove2.me/theorems/9cc63017-022d-4894-b19b-4002d158d6d1
-- title:
--   Tanner Lifted Product: lps Theta Square LSeries summable
-- statement:
--   The actual LPS coefficient-square L-series converges absolutely for Re(s) greater than two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaSquareMean.lean#L64-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaSquareMean.lean#L64-L68

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaSquareMean
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsThetaSquareLSeries_summable (q : ℕ) [Fact q.Prime]
    (hq4 : q%4=1) (s : ℂ) (hs : 2<s.re) :
    LSeriesSummable (fun n : ℕ => (lpsThetaSquareCoeff q hq4 n:ℂ)) s := by sorry
