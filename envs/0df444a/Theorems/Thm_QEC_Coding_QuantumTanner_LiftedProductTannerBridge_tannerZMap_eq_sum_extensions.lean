-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_tannerZMap_eq_sum_extensions
-- name    : QEC.Coding.QuantumTanner.LiftedProductTannerBridge.tannerZMap_eq_sum_extensions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:11:39.174211+00:00
-- url     : https://prove2.me/theorems/cc010f75-1d84-4c61-959d-b2d0c25ef510
-- title:
--   Lifted Product Tanner Bridge: tanner ZMap eq sum extensions
-- statement:
--   The Lifted Product Tanner Bridge construction uses the tanner ZMap eq sum extensions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L233-L240
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L233-L240

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

theorem QEC.Coding.QuantumTanner.LiftedProductTannerBridge.tannerZMap_eq_sum_extensions (a : A → G) (b : B → G)
    (L : LinearCode (ZMod 2) (A × B)) (T : (G → L.carrier) × (G → L.carrier)) :
    tannerZMap a b L T =
      (∑ u : G, chartExtension a b false true u (T.1 u).val) +
      (∑ u : G, chartExtension a b true false u (T.2 u).val) := by sorry
