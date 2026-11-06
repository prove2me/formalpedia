-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumChannel_traceNorm_mapDensity_eq_one
-- name    : QEC.Semantics.QuantumChannel.traceNorm_mapDensity_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:58:33.303286+00:00
-- url     : https://prove2.me/theorems/a564f31f-9f11-4aea-a1a1-8913dbd18439
-- title:
--   Quantum Channel: trace Norm map Density eq one
-- statement:
--   The Quantum Channel construction uses the trace Norm map Density eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/TraceNorm.lean#L67-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/TraceNorm.lean#L67-L70

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

theorem QEC.Semantics.QuantumChannel.traceNorm_mapDensity_eq_one [Nontrivial K]
    (Phi : QuantumChannel H K) (rho : DensityOperator H) :
    traceNorm (Phi rho.toOperator) = 1 := by sorry
