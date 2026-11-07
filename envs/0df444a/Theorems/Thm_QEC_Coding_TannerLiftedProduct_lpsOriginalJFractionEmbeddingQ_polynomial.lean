-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionEmbeddingQ_polynomial
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJFractionEmbeddingQ_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:57:42.207674+00:00
-- url     : https://prove2.me/theorems/d25fcad9-2af9-484f-91fc-180eefbeea3b
-- title:
--   Tanner Lifted Product: lps Original JFraction Embedding Q polynomial
-- statement:
--   Actual fraction-field embedding on polynomials recovers the SAME original rational j evaluation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalFunctionField.lean#L87-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalFunctionField.lean#L87-L91

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJFractionEmbeddingQ_polynomial (P : Polynomial ℚ) :
    lpsOriginalJFractionEmbeddingQ (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) P)=
      algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
        (lpsOriginalJHolomorphicEvalQ P) := by sorry
