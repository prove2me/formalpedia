-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalIntegerReciprocalBaseFractionMap_injective
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerReciprocalBaseFractionMap_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:27:27.025785+00:00
-- url     : https://prove2.me/theorems/d6d5fe77-72fb-4ee6-9c70-52e900985053
-- title:
--   Tanner Lifted Product: lps Original Integer Reciprocal Base Fraction Map injective
-- statement:
--   The Tanner Lifted Product construction uses the lps Original Integer Reciprocal Base Fraction Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelCharts.lean#L91-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelCharts.lean#L91-L94

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerReciprocalBaseFractionMap_injective :
    Function.Injective lpsOriginalIntegerReciprocalBaseFractionMap := by sorry
