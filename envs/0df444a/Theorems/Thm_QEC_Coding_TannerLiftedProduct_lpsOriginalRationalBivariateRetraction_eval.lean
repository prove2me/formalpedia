-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalBivariateRetraction_eval
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalBivariateRetraction_eval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:59:47.596773+00:00
-- url     : https://prove2.me/theorems/c90cad65-322a-48f1-83a2-d36926e24c31
-- title:
--   Tanner Lifted Product: lps Original Rational Bivariate Retraction eval
-- statement:
--   Literal evaluation of the transferred rational bivariate polynomial as finite original-support scalar sums.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L516-L528
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L516-L528

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalBivariateRetraction_eval
    (P : Polynomial (Polynomial ℂ)) (x y : ℂ) :
    (lpsOriginalRationalBivariateRetraction P).eval₂
      ((Polynomial.evalRingHom x).comp (Polynomial.mapRingHom (algebraMap ℚ ℂ))) y=
      ∑ k∈P.support,∑ i∈(P.coeff k).support,
        (lpsOriginalRationalRetraction ((P.coeff k).coeff i):ℂ)*x^i*y^k := by sorry
