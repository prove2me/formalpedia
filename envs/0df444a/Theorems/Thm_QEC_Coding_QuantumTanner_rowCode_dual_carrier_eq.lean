-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_rowCode_dual_carrier_eq
-- name    : QEC.Coding.QuantumTanner.rowCode_dual_carrier_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:09:47.506357+00:00
-- url     : https://prove2.me/theorems/36f6caa6-5091-4d0e-903b-ba0af12ec182
-- title:
--   Quantum Tanner: row Code dual carrier eq
-- statement:
--   Row constraints dualize row by row.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDuality.lean#L81-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDuality.lean#L81-L106

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDuality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.rowCode_dual_carrier_eq (CB : LinearCode F B) :
    (rowCode (A := A) CB).dual.carrier = (rowCode (A := A) CB.dual).carrier := by sorry
