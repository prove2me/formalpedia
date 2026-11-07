-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductActionBridge_x_auxiliary_entry
-- name    : QEC.Coding.QuantumTanner.LiftedProductActionBridge.x_auxiliary_entry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:10:19.365571+00:00
-- url     : https://prove2.me/theorems/0b507531-4f86-4636-a79f-394957282caa
-- title:
--   Lifted Product Action Bridge: x auxiliary entry
-- statement:
--   Actual X auxiliary entries retain the positive left A shift.
--   The boundary sign disappears only because the coefficient field is binary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L101-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L101-L110

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

theorem QEC.Coding.QuantumTanner.LiftedProductActionBridge.x_auxiliary_entry (hA : Matrix C A (ZMod 2)) (hB : Matrix D B (ZMod 2))
    (a : A → G) (b : B → G) (t : Bool) (d : D) (i : A) (u : G)
    (s : Bool) (c : C) (d₀ : Bool × D) (g : G) :
    boundary1Matrix (canonicalData hA hB a b) ((t, d), i, u)
        (auxiliaryCoordinate (s, c) d₀ g) =
      if (t, d) = d₀ then
        if u = (if s then (a i)⁻¹ * g else g) then hA c i else 0
      else 0 := by sorry
