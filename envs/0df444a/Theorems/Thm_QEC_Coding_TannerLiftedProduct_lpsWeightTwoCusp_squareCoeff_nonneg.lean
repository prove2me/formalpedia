-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCusp_squareCoeff_nonneg
-- name    : QEC.Coding.TannerLiftedProduct.lpsWeightTwoCusp_squareCoeff_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:42:28.842066+00:00
-- url     : https://prove2.me/theorems/3994d9a8-70b4-4fda-955d-c7683b7421ff
-- title:
--   Tanner Lifted Product: lps Weight Two Cusp square Coeff nonneg
-- statement:
--   The genuine coefficient squares are nonnegative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspSquareLSeries.lean#L23-L25
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspSquareLSeries.lean#L23-L25

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsWeightTwoCusp_squareCoeff_nonneg (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) (n : ℕ) :
    0≤lpsWeightTwoCusp_squareCoeff N f n := by sorry
