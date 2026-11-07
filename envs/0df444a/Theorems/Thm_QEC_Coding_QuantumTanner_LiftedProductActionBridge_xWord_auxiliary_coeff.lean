-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductActionBridge_xWord_auxiliary_coeff
-- name    : QEC.Coding.QuantumTanner.LiftedProductActionBridge.xWord_auxiliary_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:10:22.4268+00:00
-- url     : https://prove2.me/theorems/86427dbe-d754-4dcc-8762-65c8e3c6690b
-- title:
--   Lifted Product Action Bridge: x Word auxiliary coeff
-- statement:
--   Actual X auxiliary coefficients are the source's ordered left multiplication.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L169-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L169-L178

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductRestriction
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductActionBridge
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductActionBridge
open QEC.Coding.LiftedProduct
open QEC.Coding.QuantumTanner.LiftedProductRestriction
noncomputable section
variable {G A B C D : Type*} [Group G] [Fintype G] [DecidableEq G]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

theorem QEC.Coding.QuantumTanner.LiftedProductActionBridge.xWord_auxiliary_coeff (hA : Matrix C A (ZMod 2))
    (hB : Matrix D B (ZMod 2)) (a : A → G) (b : B → G)
    (V0 V1 : Matrix A D (MonoidAlgebra (ZMod 2) G))
    (s t : Bool) (c : C) (d : D) (g : G) :
    xWord hA hB a b (xParameter V0 V1) (auxiliaryCoordinate (s, c) (t, d) g) =
      ∑ i : A, hA c i * (if t then V1 i d else V0 i d).coeff
        (if s then (a i)⁻¹ * g else g) := by sorry
