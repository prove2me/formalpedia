-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductRestriction_selected_auxiliary_pointwise_disjoint
-- name    : QEC.Coding.QuantumTanner.LiftedProductRestriction.selected_auxiliary_pointwise_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:05:44.076751+00:00
-- url     : https://prove2.me/theorems/1a13060d-505b-4fee-9c6a-e3899c62e8ee
-- title:
--   Lifted Product Restriction: selected auxiliary pointwise disjoint
-- statement:
--   Every auxiliary coordinate has at least one selected support equal to zero.
--   No equality of retained check spaces is assumed or concluded here.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductRestriction.lean#L86-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductRestriction.lean#L86-L101

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.MonoidAlgebra.Basic
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductRestriction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductRestriction
variable {R A B C D C' D' : Type*} [Ring R]
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [Fintype C'] [Fintype D']
omit [Fintype C] [Fintype D]

theorem QEC.Coding.QuantumTanner.LiftedProductRestriction.selected_auxiliary_pointwise_disjoint
    (hA HA : Matrix C A R) (hB HB : Matrix D B R)
    (gA GA : Matrix C' A R) (gB GB : Matrix D' B R)
    (hA0 : hA * gA.transpose = 0) (hA1 : HA * GA.transpose = 0)
    (hB0 : gB * hB.transpose = 0) (hB1 : GB * HB.transpose = 0)
    (U0 U1 : Matrix C D' R) (V0 V1 : Matrix C' D R)
    (c : Bool × C) (d : Bool × D) :
    zAuxiliary hB HB (U0 * GB) (U1 * gB) c d = 0 ∨
      xAuxiliary hA HA (gA.transpose * V0) (GA.transpose * V1) c d = 0 := by sorry
