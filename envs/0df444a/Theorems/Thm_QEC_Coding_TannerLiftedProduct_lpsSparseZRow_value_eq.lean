-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSparseZRow_value_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsSparseZRow_value_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:11:25.598497+00:00
-- url     : https://prove2.me/theorems/bb80f93a-e9e9-47d9-88c3-baae6beb8ea5
-- title:
--   Tanner Lifted Product: lps Sparse ZRow value eq
-- statement:
--   Every computed Z coefficient equals the actual second-boundary transpose coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L241-L265
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L241-L265

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_980d0372b5_23

theorem QEC.Coding.TannerLiftedProduct.lpsSparseZRow_value_eq {q D r r' : ℕ} [Fact q.Prime]
    {F : Type} [Field F] [Fintype F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) (row : LPSSparseZIndex q D r')
    (qubit : LPSSparseQubitIndex q D r r') :
    lpsSparseRowValue (lpsSparseZRow label h h' row) qubit =
      LiftedProduct.boundary2Matrix
        (data (fun j => (lpsPSLEnumerationEquiv q) (label j)) h h')
        (lpsSparseQubitDecode qubit) (lpsSparseZDecode row) := by sorry
