-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_tannerZMap_range_eq_checks
-- name    : QEC.Coding.QuantumTanner.LiftedProductTannerBridge.tannerZMap_range_eq_checks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:11:32.226875+00:00
-- url     : https://prove2.me/theorems/a0b2d4b1-0c93-47af-b5bc-5db9688e1a57
-- title:
--   Lifted Product Tanner Bridge: tanner ZMap range eq checks
-- statement:
--   The Lifted Product Tanner Bridge construction uses the tanner ZMap range eq checks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L266-L288
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L266-L288

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

theorem QEC.Coding.QuantumTanner.LiftedProductTannerBridge.tannerZMap_range_eq_checks (a : A → G) (b : B → G)
    (L : LinearCode (ZMod 2) (A × B)) :
    LinearMap.range (tannerZMap a b L) = tannerZChecks a b L := by sorry
