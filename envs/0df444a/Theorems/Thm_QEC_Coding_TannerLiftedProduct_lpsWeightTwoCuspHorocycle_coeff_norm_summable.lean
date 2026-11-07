-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoCuspHorocycle_coeff_norm_summable
-- name    : QEC.Coding.TannerLiftedProduct.lpsWeightTwoCuspHorocycle_coeff_norm_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:15:29.802432+00:00
-- url     : https://prove2.me/theorems/3eb4a5ac-94e1-4689-b749-d010b4e546e4
-- title:
--   Tanner Lifted Product: lps Weight Two Cusp Horocycle coeff norm summable
-- statement:
--   The norms of actual coefficients with the positive-height exponential weight are summable.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L55-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L55-L61

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsWeightTwoCuspHorocycle_coeff_norm_summable (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) :
    Summable (fun n : ℕ => ‖PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)‖*
      (Real.exp (-2*Real.pi*y))^n) := by sorry
