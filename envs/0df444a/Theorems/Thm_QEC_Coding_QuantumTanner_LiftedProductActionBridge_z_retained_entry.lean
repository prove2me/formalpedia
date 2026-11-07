-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductActionBridge_z_retained_entry
-- name    : QEC.Coding.QuantumTanner.LiftedProductActionBridge.z_retained_entry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:09:59.190837+00:00
-- url     : https://prove2.me/theorems/fde711c7-d463-4103-9938-6aa9b42cf6b3
-- title:
--   Lifted Product Action Bridge: z retained entry
-- statement:
--   Actual Z boundary entries on the retained qubits, including the inverse A shift.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L64-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L64-L73

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

theorem QEC.Coding.QuantumTanner.LiftedProductActionBridge.z_retained_entry (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (a : A → G) (b : B → G) (s : Bool) (c : C) (b₀ : B) (u : G)
    (i : A) (j : B) (g : G) :
    boundary2Matrix (canonicalData hA hB a b) (retainedCoordinate i j g)
        (b₀, (s, c), u) =
      if j = b₀ then
        if g = (if s then (a i)⁻¹ * u else u) then hA c i else 0
      else 0 := by sorry
