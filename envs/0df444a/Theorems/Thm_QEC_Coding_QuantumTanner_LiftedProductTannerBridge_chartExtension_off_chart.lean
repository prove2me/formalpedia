-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_chartExtension_off_chart
-- name    : QEC.Coding.QuantumTanner.LiftedProductTannerBridge.chartExtension_off_chart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:22:57.418086+00:00
-- url     : https://prove2.me/theorems/b2c957c8-b666-430a-88e5-65bb4f607a48
-- title:
--   Lifted Product Tanner Bridge: chart Extension off chart
-- statement:
--   Away from that vertex neighbourhood the local extension is zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L220-L224
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L220-L224

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

theorem QEC.Coding.QuantumTanner.LiftedProductTannerBridge.chartExtension_off_chart (a : A → G) (b : B → G) (left right : Bool)
    (u : G) (x : Word (ZMod 2) (A × B)) (i : A) (j : B) (g : G)
    (h : u ≠ chartVertex a b left right i j g) :
    chartExtension a b left right u x (i, j, g) = 0 := by sorry
