-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductActionBridge_zWord_retained_coeff
-- name    : QEC.Coding.QuantumTanner.LiftedProductActionBridge.zWord_retained_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:25:38.298879+00:00
-- url     : https://prove2.me/theorems/d1d7877f-d131-4635-afaa-0a8349537ed9
-- title:
--   Lifted Product Action Bridge: z Word retained coeff
-- statement:
--   The inverse A twist in retained Z support is determined by the boundary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L133-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L133-L141

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

theorem QEC.Coding.QuantumTanner.LiftedProductActionBridge.zWord_retained_coeff (hA : Matrix C A (ZMod 2))
    (hB : Matrix D B (ZMod 2)) (a : A → G) (b : B → G)
    (U0 U1 : Matrix C B (MonoidAlgebra (ZMod 2) G)) (i : A) (j : B) (g : G) :
    zWord hA hB a b (zParameter U0 U1) (retainedCoordinate i j g) =
      (∑ c : C, hA c i * (U0 c j).coeff g) +
        ∑ c : C, hA c i * (U1 c j).coeff (a i * g) := by sorry
