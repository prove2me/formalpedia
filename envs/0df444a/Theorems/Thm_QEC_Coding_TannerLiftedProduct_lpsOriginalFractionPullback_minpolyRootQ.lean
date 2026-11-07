-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFractionPullback_minpolyRootQ
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalFractionPullback_minpolyRootQ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:06:00.656252+00:00
-- url     : https://prove2.me/theorems/3c5bb600-fb2c-4d59-91c0-ec49e1738d58
-- title:
--   Tanner Lifted Product: lps Original Fraction Pullback minpoly Root Q
-- statement:
--   The actual rational minimal polynomial vanishes at every genuine original pulled-back jN root.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactFunctionFieldDegree.lean#L254-L263
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalExactFunctionFieldDegree.lean#L254-L263

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactStabilizer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalExactFunctionFieldDegree
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalFractionPullback_minpolyRootQ (N : ℕ) [NeZero N]
    (hN : 0<N) (g : 𝒮ℒ) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    Polynomial.aeval
      (lpsOriginalFractionPullbackQ g (lpsOriginalJNInFractionField N hN))
      (minpoly (FractionRing (Polynomial ℚ)) (lpsOriginalJNInFractionField N hN))=0 := by sorry
