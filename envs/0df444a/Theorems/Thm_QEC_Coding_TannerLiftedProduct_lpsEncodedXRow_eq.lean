-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEncodedXRow_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsEncodedXRow_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:16:33.567336+00:00
-- url     : https://prove2.me/theorems/04a2af2a-44e9-4ef0-8cba-872c67def12e
-- title:
--   Tanner Lifted Product: lps Encoded XRow eq
-- statement:
--   The Tanner Lifted Product construction uses the lps Encoded XRow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L142-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L142-L152

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_93e0e40f7b_113

theorem QEC.Coding.TannerLiftedProduct.lpsEncodedXRow_eq {q D r r' s : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (e : Fin s ≃ F) (label : Fin D → LPSSparseGroupIndex q)
    (h : Matrix (Fin r) (Fin D) F) (h' : Matrix (Fin r') (Fin D) F)
    (x : LPSSparseXIndex q D r) :
    lpsEncodedXRow (encodedFieldTables e) label (h.map e.symm)
      (h'.map e.symm) x =
      (lpsSparseXRow label h h' x).map (fun entry => (entry.1, e.symm entry.2)) := by sorry
