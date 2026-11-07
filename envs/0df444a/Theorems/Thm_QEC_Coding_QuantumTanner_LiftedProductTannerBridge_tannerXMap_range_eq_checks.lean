-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_tannerXMap_range_eq_checks
-- name    : QEC.Coding.QuantumTanner.LiftedProductTannerBridge.tannerXMap_range_eq_checks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:12:49.265333+00:00
-- url     : https://prove2.me/theorems/0f45d259-c433-4731-8412-7970c7497fef
-- title:
--   Lifted Product Tanner Bridge: tanner XMap range eq checks
-- statement:
--   The Lifted Product Tanner Bridge construction uses the tanner XMap range eq checks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L290-L312
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L290-L312

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

theorem QEC.Coding.QuantumTanner.LiftedProductTannerBridge.tannerXMap_range_eq_checks (a : A → G) (b : B → G)
    (L : LinearCode (ZMod 2) (A × B)) :
    LinearMap.range (tannerXMap a b L) = tannerXChecks a b L := by sorry
