-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_tensorCode_lift_punctured
-- name    : QEC.Coding.QuantumTanner.exists_tensorCode_lift_punctured
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:48:06.47265+00:00
-- url     : https://prove2.me/theorems/27d26911-c6b8-4845-aea0-663bce3b4815
-- title:
--   Quantum Tanner: exists tensor Code lift punctured
-- statement:
--   Tensor puncturing is onto the tensor product of the actual punctured codes;
--   no lifting witness is included among the assumptions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorPuncture.lean#L64-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorPuncture.lean#L64-L86

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.exists_tensorCode_lift_punctured
    (CA : LinearCode F A) (CB : LinearCode F B)
    (removedA : Finset A) (removedB : Finset B)
    (x : Word F (KeptCoordinate removedA × KeptCoordinate removedB))
    (hx : x ∈
      (tensorCode (puncturedCode CA removedA) (puncturedCode CB removedB)).carrier) :
    ∃ z : Word F (A × B), z ∈ (tensorCode CA CB).carrier ∧
      tensorPunctureMap removedA removedB z = x := by sorry
