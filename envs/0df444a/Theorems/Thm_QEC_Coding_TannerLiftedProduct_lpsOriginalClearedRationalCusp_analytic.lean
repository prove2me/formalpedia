-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedRationalCusp_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedRationalCusp_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:04:16.145952+00:00
-- url     : https://prove2.me/theorems/8ea870b0-a6f9-4a06-9816-bbb08750a407
-- title:
--   Tanner Lifted Product: lps Original Cleared Rational Cusp analytic
-- statement:
--   Actual rational cleared cusp analyticity at zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L391-L396
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L391-L396

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedRationalCusp_analytic (N : ℕ) (hN : N≠0) (B : ℕ)
    (P : Polynomial (Polynomial ℂ)) :
    AnalyticAt ℂ (lpsOriginalClearedRationalCusp N B P) 0 := by sorry
