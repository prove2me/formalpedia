-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductActionBridge_leftRegular_single
-- name    : QEC.Coding.QuantumTanner.LiftedProductActionBridge.leftRegular_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:09:33.117863+00:00
-- url     : https://prove2.me/theorems/ee370814-7d8a-446a-aba3-1d786fdf327c
-- title:
--   Lifted Product Action Bridge: left Regular single
-- statement:
--   A group-basis left action shifts its output by left multiplication.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L46-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductActionBridge.lean#L46-L51

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
omit [Fintype G] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]

theorem QEC.Coding.QuantumTanner.LiftedProductActionBridge.leftRegular_single (k go gi : G) (r : ZMod 2) :
    leftRegularMatrix (MonoidAlgebra.single k r) go gi =
      if go = k * gi then r else 0 := by sorry
