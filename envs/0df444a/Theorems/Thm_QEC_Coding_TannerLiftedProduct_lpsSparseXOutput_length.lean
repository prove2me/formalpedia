-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSparseXOutput_length
-- name    : QEC.Coding.TannerLiftedProduct.lpsSparseXOutput_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:53:39.478762+00:00
-- url     : https://prove2.me/theorems/b74ee05c-7fd2-4d07-9cbc-6a4d21209735
-- title:
--   Tanner Lifted Product: lps Sparse XOutput length
-- statement:
--   The Tanner Lifted Product construction uses the lps Sparse XOutput length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L332-L336
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L332-L336

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_980d0372b5_23

theorem QEC.Coding.TannerLiftedProduct.lpsSparseXOutput_length {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) :
    (lpsSparseXOutput label h h').length = (2 * r) * (D * (lpsPSLList q).length) := by sorry
