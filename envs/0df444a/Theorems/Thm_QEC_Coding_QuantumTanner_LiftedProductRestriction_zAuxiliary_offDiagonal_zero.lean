-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_LiftedProductRestriction_zAuxiliary_offDiagonal_zero
-- name    : QEC.Coding.QuantumTanner.LiftedProductRestriction.zAuxiliary_offDiagonal_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:05:40.25326+00:00
-- url     : https://prove2.me/theorems/f3c86928-0e39-408b-8c55-fdfad5714fde
-- title:
--   Lifted Product Restriction: z Auxiliary off Diagonal zero
-- statement:
--   Local dual-check cancellation eliminates both off-diagonal Z blocks.
--   These local matrix identities are later derived from dual parity-check data.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductRestriction.lean#L59-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/LiftedProductRestriction.lean#L59-L67

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.MonoidAlgebra.Basic
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductRestriction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductRestriction
variable {R A B C D C' D' : Type*} [Ring R]
  [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [Fintype C'] [Fintype D']
omit [Fintype C] [Fintype D]

theorem QEC.Coding.QuantumTanner.LiftedProductRestriction.zAuxiliary_offDiagonal_zero
    (hB HB : Matrix D B R) (gB GB : Matrix D' B R)
    (h0 : gB * hB.transpose = 0) (h1 : GB * HB.transpose = 0)
    (U0 U1 : Matrix C D' R) (c : C) (d : D) :
    zAuxiliary hB HB (U0 * GB) (U1 * gB) (false, c) (true, d) = 0 ∧
      zAuxiliary hB HB (U0 * GB) (U1 * gB) (true, c) (false, d) = 0 := by sorry
