-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductActionBridge_z_auxiliary_entry
-- name    : QEC.Coding.QuantumTanner.LiftedProductActionBridge.z_auxiliary_entry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:10:09.19292+00:00
-- url     : https://prove2.me/theorems/8569185e-5269-4b79-8a8a-470403ceecec
-- title:
--   Lifted Product Action Bridge: z auxiliary entry
-- statement:
--   Actual Z auxiliary entries retain the positive right B shift.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L88-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L88-L97

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

theorem QEC.Coding.QuantumTanner.LiftedProductActionBridge.z_auxiliary_entry (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (a : A → G) (b : B → G) (s : Bool) (c : C) (j : B) (u : G)
    (c₀ : Bool × C) (t : Bool) (d : D) (g : G) :
    boundary2Matrix (canonicalData hA hB a b)
        (auxiliaryCoordinate c₀ (t, d) g) (j, (s, c), u) =
      if c₀ = (s, c) then
        if g = (if t then u * b j else u) then hB d j else 0
      else 0 := by sorry
