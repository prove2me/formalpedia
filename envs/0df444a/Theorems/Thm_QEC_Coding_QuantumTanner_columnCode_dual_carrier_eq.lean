-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_columnCode_dual_carrier_eq
-- name    : QEC.Coding.QuantumTanner.columnCode_dual_carrier_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:09:46.165593+00:00
-- url     : https://prove2.me/theorems/ed30625b-f1ae-40b0-8090-ab4f85cfac4c
-- title:
--   Quantum Tanner: column Code dual carrier eq
-- statement:
--   Column constraints dualize column by column, including empty coordinate sets.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDuality.lean#L53-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDuality.lean#L53-L78

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDuality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.columnCode_dual_carrier_eq (CA : LinearCode F A) :
    (columnCode (B := B) CA).dual.carrier = (columnCode (B := B) CA.dual).carrier := by sorry
