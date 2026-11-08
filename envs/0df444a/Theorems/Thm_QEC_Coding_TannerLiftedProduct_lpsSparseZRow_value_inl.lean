-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSparseZRow_value_inl
-- name    : QEC.Coding.TannerLiftedProduct.lpsSparseZRow_value_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:13:19.797913+00:00
-- url     : https://prove2.me/theorems/a3fa5e35-d72a-4656-ab22-4d826d8b9b37
-- title:
--   Tanner Lifted Product: lps Sparse ZRow value inl
-- statement:
--   The Tanner Lifted Product construction uses the lps Sparse ZRow value inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L127-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L127-L137

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_980d0372b5_23

theorem QEC.Coding.TannerLiftedProduct.lpsSparseZRow_value_inl {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) (row : LPSSparseZIndex q D r')
    (ac br : Fin D) (go : LPSSparseGroupIndex q) :
    lpsSparseRowValue (lpsSparseZRow label h h' row) (Sum.inl (ac, br, go)) =
      if row.1 = ac ∧ lpsPSLIndexMul q
          (lpsPSLIndexInv q (lpsSparseVoltage label (finProdFinEquiv.symm row.2.1).1 br))
          row.2.2 = go
      then h' (finProdFinEquiv.symm row.2.1).2 br else 0 := by sorry
