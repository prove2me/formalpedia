-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalLaurentPolynomialMap_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerReciprocalLaurentPolynomialMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:27:09.904536+00:00
-- url     : https://prove2.me/theorems/7d2e7828-58fb-42e5-bef1-c4454126de66
-- title:
--   Tanner Lifted Product: lps Original Integer Reciprocal Laurent Polynomial Map injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Reciprocal Laurent Polynomial Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelCharts.lean#L389-L391
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelCharts.lean#L389-L391

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerReciprocalLaurentPolynomialMap_injective :
    Function.Injective lpsOriginalIntegerReciprocalLaurentPolynomialMap := by sorry
