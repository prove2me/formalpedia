-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCusp_squareCoeff_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsWeightTwoCusp_squareCoeff_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:42:31.091372+00:00
-- url     : https://prove2.me/theorems/dce59b86-3592-45b3-bb54-71846ec481bd
-- title:
--   Tanner Lifted Product: lps Weight Two Cusp square Coeff zero
-- statement:
--   The actual cusp form has zero constant square coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspSquareLSeries.lean#L28-L34
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspSquareLSeries.lean#L28-L34

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsWeightTwoCusp_squareCoeff_zero (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsWeightTwoCusp_squareCoeff N f 0=0 := by sorry
