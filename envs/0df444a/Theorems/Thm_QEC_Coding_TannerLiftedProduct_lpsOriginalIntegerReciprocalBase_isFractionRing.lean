-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalBase_isFractionRing
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerReciprocalBase_isFractionRing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:28:19.563143+00:00
-- url     : https://prove2.me/theorems/e4df7e4f-8150-44cd-bcb5-e39ea81f971f
-- title:
--   Tanner Lifted Product: lps Original Integer Reciprocal Base is Fraction Ring
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Reciprocal Base is Fraction Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelCharts.lean#L96-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelCharts.lean#L96-L115

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerReciprocalBase_isFractionRing :
    letI := lpsOriginalIntegerReciprocalBaseFractionMap.toAlgebra
    IsFractionRing (Polynomial ℤ) (FractionRing (Polynomial ℚ)) := by sorry
