-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalLaurent_isLocalization
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerReciprocalLaurent_isLocalization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:26:56.796949+00:00
-- url     : https://prove2.me/theorems/bd96ec08-6d65-471d-9054-cad54f09c070
-- title:
--   Tanner Lifted Product: lps Original Integer Reciprocal Laurent is Localization
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Reciprocal Laurent is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelCharts.lean#L393-L422
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelCharts.lean#L393-L422

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerReciprocalLaurent_isLocalization :
    letI := lpsOriginalIntegerReciprocalLaurentPolynomialMap.toAlgebra
    IsLocalization.Away (Polynomial.X : Polynomial ℤ) (LaurentPolynomial ℤ) := by sorry
