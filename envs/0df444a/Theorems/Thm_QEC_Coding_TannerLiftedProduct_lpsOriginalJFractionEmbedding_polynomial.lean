-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionEmbedding_polynomial
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJFractionEmbedding_polynomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:56:26.866212+00:00
-- url     : https://prove2.me/theorems/0525c928-56be-4225-8152-b8ec83e887cb
-- title:
--   Tanner Lifted Product: lps Original JFraction Embedding polynomial
-- statement:
--   Actual fraction embedding on every polynomial equals genuine j evaluation followed by localization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFunctionField.lean#L122-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFunctionField.lean#L122-L126

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJFractionEmbedding_polynomial (P : Polynomial ℂ) :
    lpsOriginalJFractionEmbedding (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) P)=
      algebraMap LPSOriginalHolomorphicRing LPSOriginalHolomorphicFractionField
        (lpsOriginalJHolomorphicEval P) := by sorry
