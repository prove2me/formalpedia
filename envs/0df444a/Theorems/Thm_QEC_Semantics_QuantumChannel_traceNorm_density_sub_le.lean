-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumChannel_traceNorm_density_sub_le
-- name    : QEC.Semantics.QuantumChannel.traceNorm_density_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:57:13.445639+00:00
-- url     : https://prove2.me/theorems/89f91fe3-e3ce-4326-99ad-02b375d24ad2
-- title:
--   Quantum Channel: trace Norm density sub le
-- statement:
--   The Quantum Channel construction uses the trace Norm density sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/TraceNorm.lean#L72-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/TraceNorm.lean#L72-L79

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

theorem QEC.Semantics.QuantumChannel.traceNorm_density_sub_le [Nontrivial H] [Nontrivial K]
    (Phi : QuantumChannel H K) (rho sigma : DensityOperator H) :
    traceNorm (Phi rho.toOperator - Phi sigma.toOperator) ≤
      traceNorm (rho.toOperator - sigma.toOperator) := by sorry
