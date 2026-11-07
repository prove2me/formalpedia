-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_mem_dualTensorCode_of_column
-- name    : QEC.Coding.QuantumTanner.mem_dualTensorCode_of_column
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:55:19.879265+00:00
-- url     : https://prove2.me/theorems/a8f03a2e-9251-49f0-bd29-488ebdfa35b0
-- title:
--   Quantum Tanner: mem dual Tensor Code of column
-- statement:
--   The Quantum Tanner construction uses the mem dual Tensor Code of column property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Core.lean#L78-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/Core.lean#L78-L82

import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_CSS_ParityChecks
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_QuantumTanner_Core
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v

theorem QEC.Coding.QuantumTanner.mem_dualTensorCode_of_column {F : Type u} {A B : Type v} [Field F] [Fintype F]
    [Fintype A] [Fintype B] (CA : LinearCode F A) (CB : LinearCode F B)
    {x : Word F (A × B)} (hx : ∀ b, columnRestriction b x ∈ CA.carrier) :
    x ∈ (dualTensorCode CA CB).carrier := by sorry
