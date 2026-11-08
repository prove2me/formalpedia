-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSparseZOutput_pairs
-- name    : QEC.Coding.TannerLiftedProduct.lpsSparseZOutput_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T10:55:28.419592+00:00
-- url     : https://prove2.me/theorems/df6219f5-6858-4143-81a2-ebe2b88fe447
-- title:
--   Tanner Lifted Product: lps Sparse ZOutput pairs
-- statement:
--   Exact emitted Z pair count; this is output size, not running time.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L405-L410
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSSparseCSS.lean#L405-L410

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEffectivePrime
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSparseCSS
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_980d0372b5_23

theorem QEC.Coding.TannerLiftedProduct.lpsSparseZOutput_pairs {q D r r' : ℕ} [Fact q.Prime] {F : Type} [Field F]
    (label : Fin D → LPSSparseGroupIndex q) (h : Matrix (Fin r) (Fin D) F)
    (h' : Matrix (Fin r') (Fin D) F) :
    ((lpsSparseZOutput label h h').map List.length).sum =
      (D * ((2 * r') * (lpsPSLList q).length)) * (D + 2 * r) := by sorry
