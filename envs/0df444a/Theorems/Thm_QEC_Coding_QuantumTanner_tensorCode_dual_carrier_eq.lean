-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_tensorCode_dual_carrier_eq
-- name    : QEC.Coding.QuantumTanner.tensorCode_dual_carrier_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:09:40.29249+00:00
-- url     : https://prove2.me/theorems/f5ce1539-c617-4f72-b4eb-2cf0a3b56b2e
-- title:
--   Quantum Tanner: tensor Code dual carrier eq
-- statement:
--   The orthogonal complement of the tensor intersection is the row/column sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDuality.lean#L109-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDuality.lean#L109-L114

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDuality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.tensorCode_dual_carrier_eq (CA : LinearCode F A) (CB : LinearCode F B) :
    (tensorCode CA CB).dual.carrier = (dualTensorCode CA.dual CB.dual).carrier := by sorry
