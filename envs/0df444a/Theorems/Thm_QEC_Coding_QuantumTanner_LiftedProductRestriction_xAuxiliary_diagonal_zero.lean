-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductRestriction_xAuxiliary_diagonal_zero
-- name    : QEC.Coding.QuantumTanner.LiftedProductRestriction.xAuxiliary_diagonal_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:05:40.706695+00:00
-- url     : https://prove2.me/theorems/1e5db46a-96da-42c2-b84f-02e731414e82
-- title:
--   Lifted Product Restriction: x Auxiliary diagonal zero
-- statement:
--   Local dual-check cancellation eliminates both diagonal X blocks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductRestriction.lean#L71-L81
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductRestriction.lean#L71-L81

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.MonoidAlgebra.Basic
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductRestriction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductRestriction
variable {R A B C D C' D' : Type*} [Ring R]
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [Fintype C'] [Fintype D']
omit [Fintype C] [Fintype D]

theorem QEC.Coding.QuantumTanner.LiftedProductRestriction.xAuxiliary_diagonal_zero
    (hA HA : Matrix C A R) (gA GA : Matrix C' A R)
    (h0 : hA * gA.transpose = 0) (h1 : HA * GA.transpose = 0)
    (V0 V1 : Matrix C' D R) (c : C) (d : D) :
    xAuxiliary hA HA (gA.transpose * V0) (GA.transpose * V1)
        (false, c) (false, d) = 0 ∧
      xAuxiliary hA HA (gA.transpose * V0) (GA.transpose * V1)
        (true, c) (true, d) = 0 := by sorry
