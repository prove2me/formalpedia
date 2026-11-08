-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_encodedSparseRowValue_map_equiv
-- name    : QEC.Coding.TannerLiftedProduct.encodedSparseRowValue_map_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:15:59.396265+00:00
-- url     : https://prove2.me/theorems/23be9f97-ea7f-4ace-a404-4a107e58ca3f
-- title:
--   Tanner Lifted Product: encoded Sparse Row Value map equiv
-- statement:
--   The Tanner Lifted Product construction uses the encoded Sparse Row Value map equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L264-L273
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L264-L273

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_93e0e40f7b_113

theorem QEC.Coding.TannerLiftedProduct.encodedSparseRowValue_map_equiv {Q Q' : Type} [DecidableEq Q] [DecidableEq Q']
    {s : ℕ} (t : EncodedFieldTables s) (e : Q ≃ Q') (row : List (Q × Fin s)) (x : Q) :
    encodedSparseRowValue t (row.map fun entry => (e entry.1, entry.2)) (e x) =
      encodedSparseRowValue t row x := by sorry
