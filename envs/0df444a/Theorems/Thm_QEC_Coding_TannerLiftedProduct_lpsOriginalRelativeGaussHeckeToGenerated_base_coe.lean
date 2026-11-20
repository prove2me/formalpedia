-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRelativeGaussHeckeToGenerated_base_coe
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeToGenerated_base_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T10:23:57.161102+00:00
-- url     : https://prove2.me/theorems/4a47cfa1-f0b6-4efb-9f79-a9af7844c6ef
-- title:
--   Tanner Lifted Product: lps Original Relative Gauss Hecke To Generated base coe
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Relative Gauss Hecke To Generated base coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussNormalization.lean#L343-L365
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRelativeGaussNormalization.lean#L343-L365

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGaussResidueCoordinate
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalPrimeRelativeMinpoly
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRelativeGaussNormalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRelativeGaussHeckeToGenerated_base_coe
    (N p : ℕ) [NeZero N] [NeZero p] [NeZero (N*p)] [Fact p.Prime]
    (hNp : p.Coprime N) (h4N : 4 ∣ N) (hN : 0 < N)
    (c : LPSOriginalGaussAffineOrder N hN p) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    (lpsOriginalRelativeGaussHeckeToGenerated N p hNp h4N hN
      (AdjoinRoot.of (lpsOriginalRelativeGaussHeckePolynomial N hN p) c)).val =
      (lpsOriginalGaussAffineToGenerated N hN p c).val := by sorry
