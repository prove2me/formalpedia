-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductActionBridge_xWord_retained_coeff
-- name    : QEC.Coding.QuantumTanner.LiftedProductActionBridge.xWord_retained_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:25:49.80503+00:00
-- url     : https://prove2.me/theorems/d4d9c9e9-ac9f-45ee-ad91-35c99880e0b6
-- title:
--   Lifted Product Action Bridge: x Word retained coeff
-- statement:
--   The inverse B twist in retained X support is determined by the transpose.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L144-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L144-L152

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

theorem QEC.Coding.QuantumTanner.LiftedProductActionBridge.xWord_retained_coeff (hA : Matrix C A (ZMod 2))
    (hB : Matrix D B (ZMod 2)) (a : A → G) (b : B → G)
    (V0 V1 : Matrix A D (MonoidAlgebra (ZMod 2) G)) (i : A) (j : B) (g : G) :
    xWord hA hB a b (xParameter V0 V1) (retainedCoordinate i j g) =
      (∑ d : D, hB d j * (V0 i d).coeff g) +
        ∑ d : D, hB d j * (V1 i d).coeff (g * b j) := by sorry
