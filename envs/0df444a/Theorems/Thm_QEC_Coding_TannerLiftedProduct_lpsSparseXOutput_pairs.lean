-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSparseXOutput_pairs
-- name    : QEC.Coding.TannerLiftedProduct.lpsSparseXOutput_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:55:28.573051+00:00
-- url     : https://prove2.me/theorems/39958bc5-5a77-4eaf-9496-fa6c165dae5c
-- title:
--   Tanner Lifted Product: lps Sparse XOutput pairs
-- statement:
--   Exact emitted X pair count; this is output size, not running time.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L397-L402
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L397-L402

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_980d0372b5_23

theorem QEC.Coding.TannerLiftedProduct.lpsSparseXOutput_pairs {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) :
    ((lpsSparseXOutput label h h').map List.length).sum =
      ((2 * r) * (D * (lpsPSLList q).length)) * (D + 2 * r') := by sorry
