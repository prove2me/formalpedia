-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumChannel_traceNorm_comp_apply_le_of_isSymmetric
-- name    : QEC.Semantics.QuantumChannel.traceNorm_comp_apply_le_of_isSymmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:00:48.118854+00:00
-- url     : https://prove2.me/theorems/d1f4868b-32f3-491d-8c56-f700eeed30e0
-- title:
--   Quantum Channel: trace Norm comp apply le of is Symmetric
-- statement:
--   The Quantum Channel construction uses the trace Norm comp apply le of is Symmetric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/TraceNorm.lean#L81-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/TraceNorm.lean#L81-L90

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

theorem QEC.Semantics.QuantumChannel.traceNorm_comp_apply_le_of_isSymmetric
    [Nontrivial H] [Nontrivial K] [Nontrivial L]
    (Psi : QuantumChannel K L) (Phi : QuantumChannel H K)
    (A : Operator H) (hA : A.IsSymmetric) :
    traceNorm ((comp Psi Phi) A) ≤ traceNorm A := by sorry
