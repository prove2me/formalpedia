-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductActionBridge_full_checks_orthogonal
-- name    : QEC.Coding.QuantumTanner.LiftedProductActionBridge.full_checks_orthogonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:10:46.219048+00:00
-- url     : https://prove2.me/theorems/23d2d32a-3cff-4a03-9c2e-6f73b862c46d
-- title:
--   Lifted Product Action Bridge: full checks orthogonal
-- statement:
--   The canonical full checks commute, by the actual lifted-product chain identity.
--   There is no spectral, no-conjugacy, or group-commutativity premise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L235-L242
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L235-L242

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
variable {C' D' : Type*} [Fintype C'] [Fintype D']

theorem QEC.Coding.QuantumTanner.LiftedProductActionBridge.full_checks_orthogonal (hA : Matrix C A (ZMod 2))
    (hB : Matrix D B (ZMod 2)) (a : A → G) (b : B → G)
    (U : C2Index B (Bool × C) G → ZMod 2)
    (V : C0Index (Bool × D) A G → ZMod 2) :
    dotProduct (zWord hA hB a b U) (xWord hA hB a b V) = 0 := by sorry
