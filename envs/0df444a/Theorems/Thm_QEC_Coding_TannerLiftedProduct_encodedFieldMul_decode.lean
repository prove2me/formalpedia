-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_encodedFieldMul_decode
-- name    : QEC.Coding.TannerLiftedProduct.encodedFieldMul_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:15:04.092216+00:00
-- url     : https://prove2.me/theorems/54e2c6d0-535b-455a-ba64-6a4c2d32c294
-- title:
--   Tanner Lifted Product: encoded Field Mul decode
-- statement:
--   The Tanner Lifted Product construction uses the encoded Field Mul decode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L47-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L47-L49

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.encodedFieldMul_decode {F : Type} [Field F] {s : ℕ} (e : Fin s ≃ F)
    (a b : Fin s) : e (encodedFieldMul (encodedFieldTables e) a b) = e a * e b := by sorry
