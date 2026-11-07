-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_matrixRowCode_eq_dual_kernel
-- name    : QEC.Coding.QuantumTanner.LiftedProductTannerBridge.matrixRowCode_eq_dual_kernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:09:38.018198+00:00
-- url     : https://prove2.me/theorems/6089e0bd-6791-4344-9229-7fb09163e25c
-- title:
--   Lifted Product Tanner Bridge: matrix Row Code eq dual kernel
-- statement:
--   Ordinary finite-field parity-check duality, in the matrix interface used here.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L315-L318
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L315-L318

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

theorem QEC.Coding.QuantumTanner.LiftedProductTannerBridge.matrixRowCode_eq_dual_kernel (P : Matrix C A (ZMod 2)) :
    matrixRowCode P = (parityCheckKernelCode (Matrix.toLin' P)).dual := by sorry
