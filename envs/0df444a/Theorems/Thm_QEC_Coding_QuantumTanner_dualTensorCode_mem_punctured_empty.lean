-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_dualTensorCode_mem_punctured_empty
-- name    : QEC.Coding.QuantumTanner.dualTensorCode_mem_punctured_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:12:56.274141+00:00
-- url     : https://prove2.me/theorems/b8d4fd7b-6655-4598-b990-0eb2cc05aa96
-- title:
--   Quantum Tanner: dual Tensor Code mem punctured empty
-- statement:
--   Restricting both coordinates along empty punctures preserves actual
--   membership in the row/column sum code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/RobustnessTransport.lean#L61-L74
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/RobustnessTransport.lean#L61-L74

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_QuantumTanner_RobustnessTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v

theorem QEC.Coding.QuantumTanner.dualTensorCode_mem_punctured_empty
    {A B : Type v} [Fintype A] [Fintype B]
    (CA : LinearCode (ZMod 2) A) (CB : LinearCode (ZMod 2) B)
    (x : Word (ZMod 2) (A × B)) (hx : x ∈ (dualTensorCode CA CB).carrier) :
    (fun ab : KeptCoordinate (∅ : Finset A) × KeptCoordinate (∅ : Finset B) =>
      x (ab.1.1, ab.2.1)) ∈ (dualTensorCode (puncturedCode CA ∅) (puncturedCode CB ∅)).carrier := by sorry
