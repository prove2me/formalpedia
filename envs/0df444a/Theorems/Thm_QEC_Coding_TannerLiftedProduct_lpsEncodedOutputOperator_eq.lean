-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsEncodedOutputOperator_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsEncodedOutputOperator_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:17:00.164569+00:00
-- url     : https://prove2.me/theorems/0d6f2d47-162f-4e74-921b-fed23faf1e1e
-- title:
--   Tanner Lifted Product: lps Encoded Output Operator eq
-- statement:
--   The Tanner Lifted Product construction uses the lps Encoded Output Operator eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L383-L397
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSEncodedChecks.lean#L383-L397

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEncodedChecks
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_93e0e40f7b_113
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_93e0e40f7b_307
open FiniteFieldPauli

theorem QEC.Coding.TannerLiftedProduct.lpsEncodedOutputOperator_eq {q D r r' s : ℕ} [Fact q.Prime]
    {F : Type} [Field F] [Fintype F] (e : Fin s ≃ F)
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F)
    (i : Fin (((2 * r) * (D * (lpsPSLList q).length)) * s +
        (D * ((2 * r') * (lpsPSLList q).length)) * s)) :
    lpsEncodedOutputOperator e (encodedFieldTables e) label (h.map e.symm) (h'.map e.symm) i =
      ((semanticPresentation (fun j => (lpsPSLEnumerationEquiv q) (label j)) h h').checks
        (lpsEncodedCheckDecode e (lpsEncodedCheckNumbering.symm i))).globalOperator := by sorry
