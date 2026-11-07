-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJFractionInversion_involutive
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJFractionInversion_involutive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T02:27:25.359808+00:00
-- url     : https://prove2.me/theorems/523e95de-bfb4-43b4-a4e4-0c98b94defa9
-- title:
--   Tanner Lifted Product: lps Original JFraction Inversion involutive
-- statement:
--   The Tanner Lifted Product construction uses the lps Original JFraction Inversion involutive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelCharts.lean#L56-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalIntegerModelCharts.lean#L56-L85

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerAffineModel
import Mathlib.Algebra.Polynomial.Laurent
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJFractionInversion_involutive :
    Function.Involutive lpsOriginalJFractionInversion := by sorry
