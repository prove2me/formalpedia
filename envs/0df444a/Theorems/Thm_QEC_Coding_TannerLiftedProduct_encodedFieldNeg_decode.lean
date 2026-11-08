-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_encodedFieldNeg_decode
-- name    : QEC.Coding.TannerLiftedProduct.encodedFieldNeg_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:15:52.223887+00:00
-- url     : https://prove2.me/theorems/449a10eb-78a6-4dfa-8d29-e33726d31bce
-- title:
--   Tanner Lifted Product: encoded Field Neg decode
-- statement:
--   The Tanner Lifted Product construction uses the encoded Field Neg decode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L109-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L109-L111

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.encodedFieldNeg_decode {F : Type} [Field F] {s : ℕ} (e : Fin s ≃ F)
    (a : Fin s) : e (encodedFieldNeg (encodedFieldTables e) a) = -e a := by sorry
