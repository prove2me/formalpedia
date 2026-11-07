-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_columnWeight_le_of_row_support
-- name    : QEC.Coding.QuantumTanner.columnWeight_le_of_row_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:48:11.710206+00:00
-- url     : https://prove2.me/theorems/234af61b-42d0-40d6-9623-890dfd32989b
-- title:
--   Quantum Tanner: column Weight le of row support
-- statement:
--   Row support bounds the weight of every column.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/NormalViews.lean#L33-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/NormalViews.lean#L33-L40

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_NormalViews
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe v
variable {A B : Type v} [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.columnWeight_le_of_row_support
    (r : Word (ZMod 2) (A × B)) (rows : Finset A)
    (hSupport : ∀ a, a ∉ rows → rowRestriction a r = 0) (b : B) :
    HammingWeight (columnRestriction b r) ≤ rows.card := by sorry
