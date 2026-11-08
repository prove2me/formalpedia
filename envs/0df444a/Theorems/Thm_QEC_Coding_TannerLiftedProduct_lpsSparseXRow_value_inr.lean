-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSparseXRow_value_inr
-- name    : QEC.Coding.TannerLiftedProduct.lpsSparseXRow_value_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:12:51.565455+00:00
-- url     : https://prove2.me/theorems/59b21b8d-1e2e-4764-bdff-87b5ce04b5b1
-- title:
--   Tanner Lifted Product: lps Sparse XRow value inr
-- statement:
--   The Tanner Lifted Product construction uses the lps Sparse XRow value inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L116-L125
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L116-L125

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_980d0372b5_23

theorem QEC.Coding.TannerLiftedProduct.lpsSparseXRow_value_inr {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) (row : LPSSparseXIndex q D r)
    (ar : Fin (2 * r)) (bc : Fin (2 * r')) (gi : LPSSparseGroupIndex q) :
    lpsSparseRowValue (lpsSparseXRow label h h' row) (Sum.inr (ar, bc, gi)) =
      if row.1 = ar ∧ lpsPSLIndexMul q
          (lpsSparseVoltage label (finProdFinEquiv.symm bc).1 row.2.1) row.2.2 = gi
      then -h' (finProdFinEquiv.symm bc).2 row.2.1 else 0 := by sorry
