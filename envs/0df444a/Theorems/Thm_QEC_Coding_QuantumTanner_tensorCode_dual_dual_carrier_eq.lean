-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_tensorCode_dual_dual_carrier_eq
-- name    : QEC.Coding.QuantumTanner.tensorCode_dual_dual_carrier_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:14:11.642586+00:00
-- url     : https://prove2.me/theorems/292cf939-9911-45de-9eb8-76cd2320828b
-- title:
--   Quantum Tanner: tensor Code dual dual carrier eq
-- statement:
--   In particular, the tensor of dual codes has the primal row/column sum as dual.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDuality.lean#L117-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorDuality.lean#L117-L119

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_Core_Duality
import Definitions.Def_QEC_Coding_QuantumTanner_TensorDuality
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.tensorCode_dual_dual_carrier_eq (CA : LinearCode F A) (CB : LinearCode F B) :
    (tensorCode CA.dual CB.dual).dual.carrier = (dualTensorCode CA CB).carrier := by sorry
