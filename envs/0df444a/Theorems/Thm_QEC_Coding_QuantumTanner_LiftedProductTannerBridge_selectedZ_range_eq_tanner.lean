-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_selectedZ_range_eq_tanner
-- name    : QEC.Coding.QuantumTanner.LiftedProductTannerBridge.selectedZ_range_eq_tanner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:10:52.606607+00:00
-- url     : https://prove2.me/theorems/bcee3989-8e6e-4d72-9595-d3ef846b96e7
-- title:
--   Lifted Product Tanner Bridge: selected Z range eq tanner
-- statement:
--   Exact Z check-space identification, with both image inclusions witnessed by parameters.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L116-L132
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L116-L132

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

theorem QEC.Coding.QuantumTanner.LiftedProductTannerBridge.selectedZ_range_eq_tanner (hA : Matrix C A (ZMod 2))
    (hB : Matrix D B (ZMod 2)) (gB : Matrix D' B (ZMod 2)) (a : A → G) (b : B → G) :
    Set.range (selectedZWord hA hB gB a b) =
      (LinearMap.range (tannerZMap a b (tensorCode (matrixRowCode hA) (matrixRowCode gB)))).carrier := by sorry
