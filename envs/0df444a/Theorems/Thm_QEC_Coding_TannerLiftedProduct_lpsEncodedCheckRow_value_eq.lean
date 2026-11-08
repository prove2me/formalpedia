-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEncodedCheckRow_value_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsEncodedCheckRow_value_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:16:44.506212+00:00
-- url     : https://prove2.me/theorems/3c049155-43ff-4126-91b3-b819f8b9ab47
-- title:
--   Tanner Lifted Product: lps Encoded Check Row value eq
-- statement:
--   The Tanner Lifted Product construction uses the lps Encoded Check Row value eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L195-L218
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L195-L218

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_93e0e40f7b_113

theorem QEC.Coding.TannerLiftedProduct.lpsEncodedCheckRow_value_eq {q D r r' s : ℕ} [Fact q.Prime]
    {F : Type} [Field F] [Fintype F] (e : Fin s ≃ F)
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) (c : LPSEncodedCheckIndex q D r r' s)
    (qubit : LPSSparseQubitIndex q D r r') :
    e (encodedSparseRowValue (encodedFieldTables e)
      (lpsEncodedCheckRow (encodedFieldTables e) label (h.map e.symm)
        (h'.map e.symm) c) qubit) =
      lpsPresentationCheckWord label h h' (lpsEncodedCheckDecode e c)
        (lpsSparseQubitDecode qubit) := by sorry
