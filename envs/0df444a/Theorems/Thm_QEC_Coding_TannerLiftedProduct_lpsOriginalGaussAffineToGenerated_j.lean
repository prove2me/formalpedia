-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGaussAffineToGenerated_j
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGaussAffineToGenerated_j
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T11:15:20.014404+00:00
-- url     : https://prove2.me/theorems/de81da91-ca72-4816-b005-1d881d6bfa53
-- title:
--   Tanner Lifted Product: lps Original Gauss Affine To Generated j
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Gauss Affine To Generated j property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondOrderMap.lean#L163-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussSecondOrderMap.lean#L163-L174

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondUnits
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussSecondOrderMap
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGaussAffineToGenerated_j
    (N : ℕ) [NeZero N] (hN : 0 < N) (p : ℕ) [Fact p.Prime] :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalGaussAffineToGenerated N hN p
      (AdjoinRoot.of (lpsOriginalGaussPolynomial N hN p)
        (algebraMap (Polynomial ℤ) (LPSOriginalGaussBase p) Polynomial.X))).val =
      lpsOriginalJInFractionField := by sorry
