-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSparseRows_commute
-- name    : QEC.Coding.TannerLiftedProduct.lpsSparseRows_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:13:18.887196+00:00
-- url     : https://prove2.me/theorems/dd580cdb-49a4-4701-b8dd-33deccfe248d
-- title:
--   Tanner Lifted Product: lps Sparse Rows commute
-- statement:
--   The computed sparse rows satisfy CSS commutation over every finite field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L283-L302
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L283-L302

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_980d0372b5_23

theorem QEC.Coding.TannerLiftedProduct.lpsSparseRows_commute {q D r r' : ℕ} [Fact q.Prime]
    {F : Type} [Field F] [Fintype F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F)
    (x : LPSSparseXIndex q D r) (z : LPSSparseZIndex q D r') :
    ∑ qubit : LPSSparseQubitIndex q D r r',
      lpsSparseRowValue (lpsSparseXRow label h h' x) qubit *
        lpsSparseRowValue (lpsSparseZRow label h h' z) qubit = 0 := by sorry
