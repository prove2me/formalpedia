-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductActionBridge_zWord_auxiliary_coeff
-- name    : QEC.Coding.QuantumTanner.LiftedProductActionBridge.zWord_auxiliary_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:10:12.490771+00:00
-- url     : https://prove2.me/theorems/71355212-2268-4e3f-bba7-d00a6a0327a4
-- title:
--   Lifted Product Action Bridge: z Word auxiliary coeff
-- statement:
--   Actual Z auxiliary coefficients are the source's ordered right multiplication.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L155-L166
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L155-L166

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

theorem QEC.Coding.QuantumTanner.LiftedProductActionBridge.zWord_auxiliary_coeff (hA : Matrix C A (ZMod 2))
    (hB : Matrix D B (ZMod 2)) (a : A → G) (b : B → G)
    (U0 U1 : Matrix C B (MonoidAlgebra (ZMod 2) G))
    (s t : Bool) (c : C) (d : D) (g : G) :
    zWord hA hB a b (zParameter U0 U1) (auxiliaryCoordinate (s, c) (t, d) g) =
      ∑ j : B, hB d j * (if s then U1 c j else U0 c j).coeff
        (if t then g * (b j)⁻¹ else g) := by sorry
