-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_sum_chartExtension
-- name    : QEC.Coding.QuantumTanner.LiftedProductTannerBridge.sum_chartExtension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:10:07.649685+00:00
-- url     : https://prove2.me/theorems/7fc67a89-ad5b-4b63-8efb-561af558fe29
-- title:
--   Lifted Product Tanner Bridge: sum chart Extension
-- statement:
--   The Lifted Product Tanner Bridge construction uses the sum chart Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L226-L231
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L226-L231

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

theorem QEC.Coding.QuantumTanner.LiftedProductTannerBridge.sum_chartExtension (a : A → G) (b : B → G) (left right : Bool)
    (L : LinearCode (ZMod 2) (A × B)) (T : G → L.carrier) :
    (∑ u : G, chartExtension a b left right u (T u).val) =
      fun (i, j, g) => (T (chartVertex a b left right i j g)).val (i, j) := by sorry
