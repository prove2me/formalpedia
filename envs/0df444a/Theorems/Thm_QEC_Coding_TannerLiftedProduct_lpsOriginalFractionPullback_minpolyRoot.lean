-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFractionPullback_minpolyRoot
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFractionPullback_minpolyRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:10:29.924404+00:00
-- url     : https://prove2.me/theorems/049fcaae-9b7e-41a1-86e2-219d1c3434cc
-- title:
--   Tanner Lifted Product: lps Original Fraction Pullback minpoly Root
-- statement:
--   The actual complex minimal polynomial vanishes at every genuinely pulled-back original jN root.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactFunctionFieldDegree.lean#L112-L121
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactFunctionFieldDegree.lean#L112-L121

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFractionPullback_minpolyRoot (N : ℕ) [NeZero N]
    (hN : 0<N) (g : 𝒮ℒ) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    Polynomial.aeval
      (lpsOriginalFractionPullback g (lpsOriginalJNInFractionField N hN))
      (minpoly (FractionRing (Polynomial ℂ)) (lpsOriginalJNInFractionField N hN))=0 := by sorry
