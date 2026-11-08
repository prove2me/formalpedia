-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_encodedSparseScalarRow_value
-- name    : QEC.Coding.TannerLiftedProduct.encodedSparseScalarRow_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:14:55.13185+00:00
-- url     : https://prove2.me/theorems/bc3ad124-a88f-4255-b276-d4389e92a367
-- title:
--   Tanner Lifted Product: encoded Sparse Scalar Row value
-- statement:
--   The Tanner Lifted Product construction uses the encoded Sparse Scalar Row value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L71-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L71-L85

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups

theorem QEC.Coding.TannerLiftedProduct.encodedSparseScalarRow_value {Q F : Type} [DecidableEq Q] [Field F]
    {s : ℕ} (e : Fin s ≃ F) (scalar : Fin s) (row : List (Q × F)) (x : Q) :
    e (encodedSparseRowValue (encodedFieldTables e)
      (encodedSparseScalarRow (encodedFieldTables e) scalar
        (row.map fun entry => (entry.1, e.symm entry.2))) x) =
        e scalar * lpsSparseRowValue row x := by sorry
