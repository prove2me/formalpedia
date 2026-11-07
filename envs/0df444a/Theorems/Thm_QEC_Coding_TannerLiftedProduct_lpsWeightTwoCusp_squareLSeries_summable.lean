-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCusp_squareLSeries_summable
-- name    : QEC.Coding.TannerLiftedProduct.lpsWeightTwoCusp_squareLSeries_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:42:46.159162+00:00
-- url     : https://prove2.me/theorems/8e9bef8f-4ce2-49fa-858a-871692e8f9c7
-- title:
--   Tanner Lifted Product: lps Weight Two Cusp square LSeries summable
-- statement:
--   The genuine coefficient-square Dirichlet series converges absolutely throughout Re(s) greater than two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspSquareLSeries.lean#L61-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspSquareLSeries.lean#L61-L67

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsWeightTwoCusp_squareLSeries_summable (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (s : ℂ) (hs : 2<s.re) :
    LSeriesSummable (fun n : ℕ => (lpsWeightTwoCusp_squareCoeff N f n:ℂ)) s := by sorry
