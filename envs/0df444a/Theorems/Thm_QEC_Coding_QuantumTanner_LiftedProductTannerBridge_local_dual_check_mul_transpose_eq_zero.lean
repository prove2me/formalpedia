-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_local_dual_check_mul_transpose_eq_zero
-- name    : QEC.Coding.QuantumTanner.LiftedProductTannerBridge.local_dual_check_mul_transpose_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:13:24.713131+00:00
-- url     : https://prove2.me/theorems/240f0717-aa8d-4908-9966-cb8d85aada94
-- title:
--   Lifted Product Tanner Bridge: local dual check mul transpose eq zero
-- statement:
--   Raw matrix orthogonality follows from the local kernel/dual specification.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L332-L345
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L332-L345

import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTensorBridge
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTannerBridge
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductTannerBridge
open Classical
open LiftedProductRestriction LiftedProductActionBridge LiftedProductTensorBridge
universe v
variable {G A B C D C' D' : Type v} [Group G] [Fintype G] [DecidableEq G]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
  [Fintype C'] [DecidableEq C'] [Fintype D'] [DecidableEq D']

theorem QEC.Coding.QuantumTanner.LiftedProductTannerBridge.local_dual_check_mul_transpose_eq_zero (h : Matrix C A (ZMod 2))
    (g : Matrix C' A (ZMod 2))
    (hDual : parityCheckKernelCode (Matrix.toLin' g) =
      (parityCheckKernelCode (Matrix.toLin' h)).dual) : g * h.transpose = 0 := by sorry
