-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_chartLink_eq_iff
-- name    : QEC.Coding.QuantumTanner.LiftedProductTannerBridge.chartLink_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:09:44.458445+00:00
-- url     : https://prove2.me/theorems/602a42ba-cb8c-4d29-a6dc-e0272fa13b79
-- title:
--   Lifted Product Tanner Bridge: chart Link eq iff
-- statement:
--   The Lifted Product Tanner Bridge construction uses the chart Link eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L179-L185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L179-L185

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

theorem QEC.Coding.QuantumTanner.LiftedProductTannerBridge.chartLink_eq_iff (a : A → G) (b : B → G) (left right : Bool)
    (u : G) (i : A) (j : B) (g : G) :
    chartLink a b left right u (i, j) = (i, j, g) ↔
      u = chartVertex a b left right i j g := by sorry
