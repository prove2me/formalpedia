-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEncodedCheckRegions_mem_iff
-- name    : QEC.Coding.TannerLiftedProduct.lpsEncodedCheckRegions_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:15:47.877202+00:00
-- url     : https://prove2.me/theorems/54ae98cf-4a67-405d-b3b9-446ba1f52f72
-- title:
--   Tanner Lifted Product: lps Encoded Check Regions mem iff
-- statement:
--   Exact support, including the zero scalar and fields whose encoded zero is not index zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L312-L337
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L312-L337

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_93e0e40f7b_113
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_93e0e40f7b_307

theorem QEC.Coding.TannerLiftedProduct.lpsEncodedCheckRegions_mem_iff {q D r r' s : ℕ} [Fact q.Prime]
    {F : Type} [Field F] [Fintype F] (e : Fin s ≃ F)
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F)
    (i : Fin (((2 * r) * (D * (lpsPSLList q).length)) * s +
        (D * ((2 * r') * (lpsPSLList q).length)) * s))
    (qubit : LPSSparseQubitIndex q D r r') :
    lpsSparseQubitNumbering qubit ∈
      (lpsEncodedCheckRegions (encodedFieldTables e) label
        (h.map e.symm) (h'.map e.symm))[i.val]'(by
          rw [lpsEncodedCheckRegions_length]; exact i.isLt) ↔
      lpsSparseQubitDecode qubit ∈
        ((semanticPresentation (fun j => (lpsPSLEnumerationEquiv q) (label j)) h h').checks
          (lpsEncodedCheckDecode e (lpsEncodedCheckNumbering.symm i))).region.selected := by sorry
