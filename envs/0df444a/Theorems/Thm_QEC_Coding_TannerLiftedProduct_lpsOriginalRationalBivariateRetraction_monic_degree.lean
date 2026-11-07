-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalBivariateRetraction_monic_degree
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalBivariateRetraction_monic_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:03:12.019521+00:00
-- url     : https://prove2.me/theorems/81fecb6d-8e8e-4764-a986-8a46ceb2baa1
-- title:
--   Tanner Lifted Product: lps Original Rational Bivariate Retraction monic degree
-- statement:
--   Actual bivariate monicity and constructed degree preservation, without minimal-degree claim.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L257-L273
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L257-L273

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalBivariateRetraction_monic_degree
    (P : Polynomial (Polynomial ℂ)) (hP : P.Monic) :
    (lpsOriginalRationalBivariateRetraction P).Monic ∧
      (lpsOriginalRationalBivariateRetraction P).natDegree=P.natDegree := by sorry
