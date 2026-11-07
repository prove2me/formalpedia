-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHorocycleTerm_fourierCoeff
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleTerm_fourierCoeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:15:44.690198+00:00
-- url     : https://prove2.me/theorems/76bd8b32-022b-4a37-9c1d-0fec5dac9fee
-- title:
--   Tanner Lifted Product: lps Cusp Horocycle Term fourier Coeff
-- statement:
--   Orthogonality gives the exact single-frequency Fourier coefficient of every true term.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L143-L155
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSCuspHorocycle.lean#L143-L155

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspHorocycle
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHorocycleTerm_fourierCoeff (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (y : ℝ) (n : ℕ) (k : ℤ) :
    fourierCoeff (lpsCuspHorocycleTerm N f y n) k=
      if (n:ℤ)=k then PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 f)*
        ((Real.exp (-2*Real.pi*y):ℂ)^n) else 0 := by sorry
