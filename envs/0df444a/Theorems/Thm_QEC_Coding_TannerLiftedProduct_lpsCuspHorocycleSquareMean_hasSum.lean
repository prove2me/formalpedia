-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleSquareMean_hasSum
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleSquareMean_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:43:44.188629+00:00
-- url     : https://prove2.me/theorems/01b0bb7e-9cd8-490a-9f98-9ecd0a71bff2
-- title:
--   Tanner Lifted Product: lps Cusp Horocycle Square Mean has Sum
-- statement:
--   The actual square mean is the sum of the genuine coefficient squares with exact four-pi exponential damping.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspSquareLSeries.lean#L102-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspSquareLSeries.lean#L102-L116

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleSquareMean_hasSum (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) :
    HasSum (fun n : ℕ => (lpsWeightTwoCusp_squareCoeff N f n:ℂ)*
      (Real.exp (-(4*Real.pi*(n:ℝ))*y):ℂ)) (lpsCuspHorocycleSquareMean N f y:ℂ) := by sorry
