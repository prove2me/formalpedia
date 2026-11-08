-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_encodedFieldAdd_decode
-- name    : QEC.Coding.TannerLiftedProduct.encodedFieldAdd_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:14:55.054802+00:00
-- url     : https://prove2.me/theorems/565c5ec7-e9f9-44c9-90c2-67397b936680
-- title:
--   Tanner Lifted Product: encoded Field Add decode
-- statement:
--   The Tanner Lifted Product construction uses the encoded Field Add decode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L43-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L43-L45

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.encodedFieldAdd_decode {F : Type} [Field F] {s : ℕ} (e : Fin s ≃ F)
    (a b : Fin s) : e (encodedFieldAdd (encodedFieldTables e) a b) = e a + e b := by sorry
