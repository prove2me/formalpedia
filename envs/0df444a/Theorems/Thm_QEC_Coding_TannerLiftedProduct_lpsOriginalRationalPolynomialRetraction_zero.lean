-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalPolynomialRetraction_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalPolynomialRetraction_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:59:23.892434+00:00
-- url     : https://prove2.me/theorems/c744616a-2d19-4066-a888-8fb298427d65
-- title:
--   Tanner Lifted Product: lps Original Rational Polynomial Retraction zero
-- statement:
--   The actual polynomial transfer sends zero to zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L226-L229
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L226-L229

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalPolynomialRetraction_zero :
    lpsOriginalRationalPolynomialRetraction 0=0 := by sorry
