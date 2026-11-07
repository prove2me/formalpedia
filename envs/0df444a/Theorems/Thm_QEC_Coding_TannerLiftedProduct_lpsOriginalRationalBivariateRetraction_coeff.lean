-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalBivariateRetraction_coeff
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalBivariateRetraction_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:03:37.983142+00:00
-- url     : https://prove2.me/theorems/b843dc1c-39a7-4497-9590-cf0d5cd31d95
-- title:
--   Tanner Lifted Product: lps Original Rational Bivariate Retraction coeff
-- statement:
--   Literal outer coefficient identity for the actual bivariate transfer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L246-L254
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L246-L254

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalBivariateRetraction_coeff (P : Polynomial (Polynomial ℂ)) (n : ℕ) :
    (lpsOriginalRationalBivariateRetraction P).coeff n=
      lpsOriginalRationalPolynomialRetraction (P.coeff n) := by sorry
