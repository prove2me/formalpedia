-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductTannerBridge_selectedZWord_coeff
-- name    : QEC.Coding.QuantumTanner.LiftedProductTannerBridge.selectedZWord_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T01:10:09.437177+00:00
-- url     : https://prove2.me/theorems/5486e50c-be9e-48fd-b2be-bd2fe9de50d5
-- title:
--   Lifted Product Tanner Bridge: selected ZWord coeff
-- statement:
--   Coefficient extraction of the actual selected Z boundary gives the two source charts.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L54-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductTannerBridge.lean#L54-L66

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

theorem QEC.Coding.QuantumTanner.LiftedProductTannerBridge.selectedZWord_coeff (hA : Matrix C A (ZMod 2))
    (hB : Matrix D B (ZMod 2)) (gB : Matrix D' B (ZMod 2))
    (a : A → G) (b : B → G)
    (U : Matrix C D' (MonoidAlgebra (ZMod 2) G) ×
      Matrix C D' (MonoidAlgebra (ZMod 2) G)) (i : A) (j : B) (g : G) :
    selectedZWord hA hB gB a b U (i, j, g) =
      (parameterSections hA gB U.1 (g * b j)).val (i, j) +
        (parameterSections hA gB U.2 (a i * g)).val (i, j) := by sorry
