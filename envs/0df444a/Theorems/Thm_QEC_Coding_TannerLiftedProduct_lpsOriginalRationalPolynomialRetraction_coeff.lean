-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalPolynomialRetraction_coeff
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalPolynomialRetraction_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:59:31.905556+00:00
-- url     : https://prove2.me/theorems/12f362f1-739f-468a-bf42-0b297a5493a6
-- title:
--   Tanner Lifted Product: lps Original Rational Polynomial Retraction coeff
-- statement:
--   Literal coefficient identity for the actual polynomial transfer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L215-L223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L215-L223

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalPolynomialRetraction_coeff (P : Polynomial ℂ) (n : ℕ) :
    (lpsOriginalRationalPolynomialRetraction P).coeff n=
      lpsOriginalRationalRetraction (P.coeff n) := by sorry
