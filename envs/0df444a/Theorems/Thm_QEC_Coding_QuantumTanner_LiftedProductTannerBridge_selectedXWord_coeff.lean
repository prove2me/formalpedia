-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_selectedXWord_coeff
-- name    : QEC.Coding.QuantumTanner.LiftedProductTannerBridge.selectedXWord_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:10:23.702498+00:00
-- url     : https://prove2.me/theorems/d48c6551-b9ec-4dd7-8b5d-a2aaaf9b19a0
-- title:
--   Lifted Product Tanner Bridge: selected XWord coeff
-- statement:
--   Coefficient extraction of the actual selected X boundary gives the other two charts.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L69-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L69-L82

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

theorem QEC.Coding.QuantumTanner.LiftedProductTannerBridge.selectedXWord_coeff (hA : Matrix C A (ZMod 2))
    (hB : Matrix D B (ZMod 2)) (gA : Matrix C' A (ZMod 2))
    (a : A → G) (b : B → G)
    (V : Matrix C' D (MonoidAlgebra (ZMod 2) G) ×
      Matrix C' D (MonoidAlgebra (ZMod 2) G)) (i : A) (j : B) (g : G) :
    selectedXWord hA hB gA a b V (i, j, g) =
      (parameterSections gA hB V.1 g).val (i, j) +
        (parameterSections gA hB V.2 (a i * g * b j)).val (i, j) := by sorry
