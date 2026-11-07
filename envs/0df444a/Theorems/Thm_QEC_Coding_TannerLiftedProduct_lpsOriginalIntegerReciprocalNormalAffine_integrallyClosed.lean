-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalNormalAffine_integrallyClosed
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerReciprocalNormalAffine_integrallyClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:27:45.185451+00:00
-- url     : https://prove2.me/theorems/6f22bf91-d204-410a-8094-f4be26113057
-- title:
--   Tanner Lifted Product: lps Original Integer Reciprocal Normal Affine integrally Closed
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Reciprocal Normal Affine integrally Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelCharts.lean#L179-L195
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelCharts.lean#L179-L195

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerReciprocalNormalAffine_integrallyClosed
    (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerReciprocalBaseFractionMap.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    IsIntegrallyClosed
      (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)) := by sorry
