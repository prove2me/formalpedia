-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalNormalOverlap_localization
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerReciprocalNormalOverlap_localization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:28:59.605036+00:00
-- url     : https://prove2.me/theorems/7bded5cd-f6dd-4804-aa22-8c994324ca84
-- title:
--   Tanner Lifted Product: lps Original Integer Reciprocal Normal Overlap localization
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Reciprocal Normal Overlap localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelCharts.lean#L495-L542
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelCharts.lean#L495-L542

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerReciprocalNormalOverlap_localization
    (N : ℕ) (hN : 0<N) :
    let := lpsOriginalJFractionEmbeddingQ.toAlgebra
  let := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
    let := (lpsOriginalIntegerReciprocalBaseToGeneratedField N hN).toAlgebra
    let := (lpsOriginalIntegerLaurentBaseToGeneratedField N hN).toAlgebra
    let := lpsOriginalIntegerReciprocalLaurentBase_scalarTower N hN
    let := (lpsOriginalIntegerReciprocalNormalChartToOverlap N hN).toAlgebra
    IsLocalization.Away
      (algebraMap (Polynomial ℤ)
        (integralClosure (Polynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)) Polynomial.X)
      (integralClosure (LaurentPolynomial ℤ) (lpsOriginalGeneratedFunctionFieldQ N hN)) := by sorry
