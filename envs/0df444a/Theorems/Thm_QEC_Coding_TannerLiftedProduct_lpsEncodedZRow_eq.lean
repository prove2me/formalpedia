-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEncodedZRow_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsEncodedZRow_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:16:01.224198+00:00
-- url     : https://prove2.me/theorems/5def62ed-0856-4618-8df3-54504d21f7f9
-- title:
--   Tanner Lifted Product: lps Encoded ZRow eq
-- statement:
--   The Tanner Lifted Product construction uses the lps Encoded ZRow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L154-L160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L154-L160

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_93e0e40f7b_113

theorem QEC.Coding.TannerLiftedProduct.lpsEncodedZRow_eq {q D r r' s : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (e : Fin s ≃ F) (label : Fin D → LPSSparseGroupIndex q)
    (h : Matrix (Fin r) (Fin D) F) (h' : Matrix (Fin r') (Fin D) F)
    (z : LPSSparseZIndex q D r') :
    lpsEncodedZRow label (h.map e.symm) (h'.map e.symm) z =
      (lpsSparseZRow label h h' z).map (fun entry => (entry.1, e.symm entry.2)) := by sorry
