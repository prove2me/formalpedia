-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_encodedSparseRowValue_decode
-- name    : QEC.Coding.TannerLiftedProduct.encodedSparseRowValue_decode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:14:45.105107+00:00
-- url     : https://prove2.me/theorems/4042fc29-5b2b-4401-9b31-42b33af42a72
-- title:
--   Tanner Lifted Product: encoded Sparse Row Value decode
-- statement:
--   The Tanner Lifted Product construction uses the encoded Sparse Row Value decode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L55-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L55-L65

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.encodedSparseRowValue_decode {Q F : Type} [DecidableEq Q] [Field F]
    {s : ℕ} (e : Fin s ≃ F) (row : List (Q × Fin s)) (x : Q) :
    e (encodedSparseRowValue (encodedFieldTables e) row x) =
      lpsSparseRowValue (row.map fun entry => (entry.1, e entry.2)) x := by sorry
