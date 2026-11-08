-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSparseZRow_value_inr
-- name    : QEC.Coding.TannerLiftedProduct.lpsSparseZRow_value_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:13:28.881217+00:00
-- url     : https://prove2.me/theorems/e615d749-a4bc-4ed0-800c-f5d26e5dd05e
-- title:
--   Tanner Lifted Product: lps Sparse ZRow value inr
-- statement:
--   The Tanner Lifted Product construction uses the lps Sparse ZRow value inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L139-L148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L139-L148

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_980d0372b5_23

theorem QEC.Coding.TannerLiftedProduct.lpsSparseZRow_value_inr {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) (row : LPSSparseZIndex q D r')
    (ar : Fin (2 * r)) (bc : Fin (2 * r')) (go : LPSSparseGroupIndex q) :
    lpsSparseRowValue (lpsSparseZRow label h h' row) (Sum.inr (ar, bc, go)) =
      if row.2.1 = bc ∧ lpsPSLIndexMul q row.2.2
          (lpsSparseVoltage label (finProdFinEquiv.symm ar).1 row.1) = go
      then h (finProdFinEquiv.symm ar).2 row.1 else 0 := by sorry
