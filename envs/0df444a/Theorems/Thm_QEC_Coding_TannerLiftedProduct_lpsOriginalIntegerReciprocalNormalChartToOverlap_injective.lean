-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalNormalChartToOverlap_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerReciprocalNormalChartToOverlap_injective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T02:39:27.436849+00:00
-- url     : https://prove2.me/theorems/bad3a6db-6298-4cad-8f93-c007f28e74a4
-- title:
--   Tanner Lifted Product: lps Original Integer Reciprocal Normal Chart To Overlap injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Reciprocal Normal Chart To Overlap injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelCharts.lean#L480-L493
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelCharts.lean#L480-L493

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerReciprocalNormalChartToOverlap_injective
    (N : ℕ) (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    letI := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
    letI := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    letI := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
    Function.Injective (lpsOriginalIntegerReciprocalNormalChartToOverlap N hN) := by sorry
