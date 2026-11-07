-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_chartExtension_at_chart
-- name    : QEC.Coding.QuantumTanner.LiftedProductTannerBridge.chartExtension_at_chart
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:23:04.158955+00:00
-- url     : https://prove2.me/theorems/da6be4f9-a424-44e1-8702-cbc61b7bb0fe
-- title:
--   Lifted Product Tanner Bridge: chart Extension at chart
-- statement:
--   The local chart in the source is inverted by left/right inverse shifts.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L212-L217
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L212-L217

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

theorem QEC.Coding.QuantumTanner.LiftedProductTannerBridge.chartExtension_at_chart (a : A → G) (b : B → G) (left right : Bool)
    (u : G) (x : Word (ZMod 2) (A × B)) (i : A) (j : B) :
    chartExtension a b left right u x
      (i, j, (if left then (a i)⁻¹ * u else u) *
        (if right then (b j)⁻¹ else 1)) = x (i, j) := by sorry
