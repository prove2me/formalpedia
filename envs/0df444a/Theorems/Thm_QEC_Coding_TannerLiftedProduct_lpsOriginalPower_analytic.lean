-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalPower_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalPower_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:55:37.96555+00:00
-- url     : https://prove2.me/theorems/7f6a9069-a01c-47dc-9fc1-f8e8926fe325
-- title:
--   Tanner Lifted Product: lps Original Power analytic
-- statement:
--   Actual analyticity at zero of every nonnegative q power.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L312-L319
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L312-L319

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalPower_analytic (n : ℕ) :
    AnalyticAt ℂ (fun q : ℂ=>q^n) 0 := by sorry
