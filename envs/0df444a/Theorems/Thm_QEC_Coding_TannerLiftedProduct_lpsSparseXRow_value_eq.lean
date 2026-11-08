-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSparseXRow_value_eq
-- name    : QEC.Coding.TannerLiftedProduct.lpsSparseXRow_value_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:12:11.809828+00:00
-- url     : https://prove2.me/theorems/7ba32ecd-5eb1-4647-96d8-4913d421b434
-- title:
--   Tanner Lifted Product: lps Sparse XRow value eq
-- statement:
--   Every computed X coefficient equals the actual first-boundary coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L205-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L205-L238

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_980d0372b5_23

theorem QEC.Coding.TannerLiftedProduct.lpsSparseXRow_value_eq {q D r r' : ℕ} [Fact q.Prime]
    {F : Type} [Field F] [Fintype F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) (row : LPSSparseXIndex q D r)
    (qubit : LPSSparseQubitIndex q D r r') :
    lpsSparseRowValue (lpsSparseXRow label h h' row) qubit =
      LiftedProduct.boundary1Matrix
        (data (fun j => (lpsPSLEnumerationEquiv q) (label j)) h h')
        (lpsSparseXDecode row) (lpsSparseQubitDecode qubit) := by sorry
