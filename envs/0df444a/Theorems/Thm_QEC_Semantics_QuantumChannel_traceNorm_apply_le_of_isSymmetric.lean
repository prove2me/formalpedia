-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumChannel_traceNorm_apply_le_of_isSymmetric
-- name    : QEC.Semantics.QuantumChannel.traceNorm_apply_le_of_isSymmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:52:45.337932+00:00
-- url     : https://prove2.me/theorems/695217e5-37ec-4700-b12b-a0beac6a21bf
-- title:
--   Quantum Channel: trace Norm apply le of is Symmetric
-- statement:
--   Finite CPTP maps contract the trace norm on self-adjoint operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/TraceNorm.lean#L40-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/TraceNorm.lean#L40-L65

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Definitions.Def_QEC_Semantics_Channels_TraceNorm
set_option autoImplicit false
universe u
open QEC QEC.Semantics
open scoped ComplexOrder
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
open QEC.Semantics.QuantumChannel
variable {K L : Type u}
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]

theorem QEC.Semantics.QuantumChannel.traceNorm_apply_le_of_isSymmetric [Nontrivial H] [Nontrivial K]
    (Phi : QuantumChannel H K) (A : Operator H) (hA : A.IsSymmetric) :
    traceNorm (Phi A) ≤ traceNorm A := by sorry
