-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleCircle_fourierCoeff_hasSum
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_fourierCoeff_hasSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:15:42.864223+00:00
-- url     : https://prove2.me/theorems/ed8dbf41-532e-4d3d-9bef-50155e9f3ac9
-- title:
--   Tanner Lifted Product: lps Cusp Horocycle Circle fourier Coeff has Sum
-- statement:
--   Bochner integration of the actual norm-summable series gives the true sum of Fourier coefficients.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L158-L183
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L158-L183

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleCircle_fourierCoeff_hasSum (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (hy : 0<y) (k : ℤ) :
    HasSum (fun n : ℕ => fourierCoeff (lpsCuspHorocycleTerm N f y n) k)
      (fourierCoeff (lpsCuspHorocycleCircle N f y) k) := by sorry
