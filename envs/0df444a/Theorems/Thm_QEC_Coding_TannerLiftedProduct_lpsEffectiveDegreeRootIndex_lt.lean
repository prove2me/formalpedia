-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEffectiveDegreeRootIndex_lt
-- name    : QEC.Coding.TannerLiftedProduct.lpsEffectiveDegreeRootIndex_lt
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T01:54:37.557189+00:00
-- url     : https://prove2.me/theorems/e4644b38-b58d-489c-ae30-cbf8f62ebf02
-- title:
--   Tanner Lifted Product: lps Effective Degree Root Index lt
-- statement:
--   The Tanner Lifted Product construction uses the lps Effective Degree Root Index lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectiveNormalization.lean#L37-L39
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEffectiveNormalization.lean#L37-L39

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternion
import Mathlib.Data.Nat.Find
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectiveNormalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.lpsEffectiveDegreeRootIndex_lt (a : LPSResiduePrime p) :
    lpsEffectiveDegreeRootIndex a < a.q := by sorry
