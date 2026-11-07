-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_chartExtension_eq_sum_single
-- name    : QEC.Coding.QuantumTanner.LiftedProductTannerBridge.chartExtension_eq_sum_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:11:00.093974+00:00
-- url     : https://prove2.me/theorems/2d2112ca-bfc2-4be6-8a7c-33e7cf396463
-- title:
--   Lifted Product Tanner Bridge: chart Extension eq sum single
-- statement:
--   The pointwise chart extension is exactly the usual finite link extension,
--   not a different definition of the desired global check space.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L189-L209
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L189-L209

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

theorem QEC.Coding.QuantumTanner.LiftedProductTannerBridge.chartExtension_eq_sum_single (a : A → G) (b : B → G) (left right : Bool)
    (u : G) (x : Word (ZMod 2) (A × B)) :
    chartExtension a b left right u x =
      ∑ ij : A × B, x ij • Pi.single (chartLink a b left right u ij) 1 := by sorry
