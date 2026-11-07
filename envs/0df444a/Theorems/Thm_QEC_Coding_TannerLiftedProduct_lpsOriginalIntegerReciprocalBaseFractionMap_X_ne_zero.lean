-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalBaseFractionMap_X_ne_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerReciprocalBaseFractionMap_X_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:27:29.834441+00:00
-- url     : https://prove2.me/theorems/818ad605-6a69-4e44-a140-12ff303d4682
-- title:
--   Tanner Lifted Product: lps Original Integer Reciprocal Base Fraction Map X ne zero
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Reciprocal Base Fraction Map X ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelCharts.lean#L425-L428
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelCharts.lean#L425-L428

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerReciprocalBaseFractionMap_X_ne_zero :
    lpsOriginalIntegerReciprocalBaseFractionMap Polynomial.X≠0 := by sorry
