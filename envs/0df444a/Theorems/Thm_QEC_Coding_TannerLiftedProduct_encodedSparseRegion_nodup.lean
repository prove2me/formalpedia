-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_encodedSparseRegion_nodup
-- name    : QEC.Coding.TannerLiftedProduct.encodedSparseRegion_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:03:35.991237+00:00
-- url     : https://prove2.me/theorems/725ccd42-41e4-4d06-acdb-70f08b3c830e
-- title:
--   Tanner Lifted Product: encoded Sparse Region nodup
-- statement:
--   The Tanner Lifted Product construction uses the encoded Sparse Region nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L101-L103
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L101-L103

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.encodedSparseRegion_nodup {n s : ℕ} (t : EncodedFieldTables s)
    (row : List (Fin n × Fin s)) : (encodedSparseRegion t row).Nodup := by sorry
