-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_local_dual_check_row_codes
-- name    : QEC.Coding.QuantumTanner.LiftedProductTannerBridge.local_dual_check_row_codes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:09:52.570088+00:00
-- url     : https://prove2.me/theorems/94b7473a-8d4c-4935-bb10-7b4955a8f6d4
-- title:
--   Lifted Product Tanner Bridge: local dual check row codes
-- statement:
--   The source's local dual-check premise determines both local generator codes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L321-L329
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L321-L329

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

theorem QEC.Coding.QuantumTanner.LiftedProductTannerBridge.local_dual_check_row_codes (h : Matrix C A (ZMod 2))
    (g : Matrix C' A (ZMod 2))
    (hDual : parityCheckKernelCode (Matrix.toLin' g) =
      (parityCheckKernelCode (Matrix.toLin' h)).dual) :
    matrixRowCode h = parityCheckKernelCode (Matrix.toLin' g) ∧
      matrixRowCode g = parityCheckKernelCode (Matrix.toLin' h) := by sorry
