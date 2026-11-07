-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_selectedX_range_eq_tanner
-- name    : QEC.Coding.QuantumTanner.LiftedProductTannerBridge.selectedX_range_eq_tanner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:09:53.93217+00:00
-- url     : https://prove2.me/theorems/038c3d84-c12a-427d-becb-1210571bb104
-- title:
--   Lifted Product Tanner Bridge: selected X range eq tanner
-- statement:
--   Exact X check-space identification, with both image inclusions witnessed by parameters.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L135-L151
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L135-L151

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

theorem QEC.Coding.QuantumTanner.LiftedProductTannerBridge.selectedX_range_eq_tanner (hA : Matrix C A (ZMod 2))
    (hB : Matrix D B (ZMod 2)) (gA : Matrix C' A (ZMod 2)) (a : A → G) (b : B → G) :
    Set.range (selectedXWord hA hB gA a b) =
      (LinearMap.range (tannerXMap a b (tensorCode (matrixRowCode gA) (matrixRowCode hB)))).carrier := by sorry
