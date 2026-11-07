-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCusp_squareCoeff_div_rpow_summable
-- name    : QEC.Coding.TannerLiftedProduct.lpsWeightTwoCusp_squareCoeff_div_rpow_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:43:40.185854+00:00
-- url     : https://prove2.me/theorems/bf7e3235-633d-4941-9287-305ac9e0dbaf
-- title:
--   Tanner Lifted Product: lps Weight Two Cusp square Coeff div rpow summable
-- statement:
--   The actual square coefficients divided by the real-power weight form a summable series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspSquareLSeries.lean#L82-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspSquareLSeries.lean#L82-L94

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsWeightTwoCusp_squareCoeff_div_rpow_summable (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (s : ℂ) (hs : 2<s.re) :
    Summable (fun n : ℕ => lpsWeightTwoCusp_squareCoeff N f n/(n:ℝ)^s.re) := by sorry
