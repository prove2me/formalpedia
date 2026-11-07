-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_pureWord_mem_tensorCode
-- name    : QEC.Coding.QuantumTanner.pureWord_mem_tensorCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:48:36.745993+00:00
-- url     : https://prove2.me/theorems/9e9c47c9-6fa8-4965-87d2-24cfaa845327
-- title:
--   Quantum Tanner: pure Word mem tensor Code
-- statement:
--   A product of two actual local-code words satisfies both tensor constraints.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorPuncture.lean#L29-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/TensorPuncture.lean#L29-L45

import Definitions.Def_QEC_Coding_QuantumTanner_Goodness
import Definitions.Def_QEC_Coding_QuantumTanner_TensorPuncture
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v
variable {F : Type u} {A B : Type v} [Field F] [Fintype F] [Fintype A] [Fintype B]

theorem QEC.Coding.QuantumTanner.pureWord_mem_tensorCode
    (CA : LinearCode F A) (CB : LinearCode F B) (a : Word F A) (b : Word F B)
    (ha : a ∈ CA.carrier) (hb : b ∈ CB.carrier) :
    (fun ab : A × B => a ab.1 * b ab.2) ∈ (tensorCode CA CB).carrier := by sorry
