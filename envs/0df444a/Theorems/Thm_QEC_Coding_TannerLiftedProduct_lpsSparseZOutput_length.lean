-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSparseZOutput_length
-- name    : QEC.Coding.TannerLiftedProduct.lpsSparseZOutput_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:54:54.169184+00:00
-- url     : https://prove2.me/theorems/eee29e35-da00-4aa3-ac05-7866fa37b516
-- title:
--   Tanner Lifted Product: lps Sparse ZOutput length
-- statement:
--   The Tanner Lifted Product construction uses the lps Sparse ZOutput length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L338-L342
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L338-L342

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_980d0372b5_23

theorem QEC.Coding.TannerLiftedProduct.lpsSparseZOutput_length {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) :
    (lpsSparseZOutput label h h').length = D * ((2 * r') * (lpsPSLList q).length) := by sorry
