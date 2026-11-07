-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_rowWeight_le_of_column_support
-- name    : QEC.Coding.QuantumTanner.rowWeight_le_of_column_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:47:20.059523+00:00
-- url     : https://prove2.me/theorems/1e681ae3-fd09-442a-9154-bb14edf9da4d
-- title:
--   Quantum Tanner: row Weight le of column support
-- statement:
--   Column support bounds the weight of every row, without any code premise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/NormalViews.lean#L23-L30
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/NormalViews.lean#L23-L30

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
variable {A B : Type v} [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.rowWeight_le_of_column_support
    (c : Word (ZMod 2) (A × B)) (columns : Finset B)
    (hSupport : ∀ b, b ∉ columns → columnRestriction b c = 0) (a : A) :
    HammingWeight (rowRestriction a c) ≤ columns.card := by sorry
