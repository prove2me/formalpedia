-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductActionBridge_x_retained_entry
-- name    : QEC.Coding.QuantumTanner.LiftedProductActionBridge.x_retained_entry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:10:06.057316+00:00
-- url     : https://prove2.me/theorems/dff716aa-3701-4f83-a27b-eaeacb24f1d3
-- title:
--   Lifted Product Action Bridge: x retained entry
-- statement:
--   Actual transposed X boundary entries: the B shift is adjointed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L76-L85
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L76-L85

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

theorem QEC.Coding.QuantumTanner.LiftedProductActionBridge.x_retained_entry (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (a : A → G) (b : B → G) (t : Bool) (d : D) (a₀ : A) (u : G)
    (i : A) (j : B) (g : G) :
    boundary1Matrix (canonicalData hA hB a b) ((t, d), a₀, u)
        (retainedCoordinate i j g) =
      if a₀ = i then
        if u = (if t then g * b j else g) then hB d j else 0
      else 0 := by sorry
