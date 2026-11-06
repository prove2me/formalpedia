-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumChannel_map_isSymmetric
-- name    : QEC.Semantics.QuantumChannel.map_isSymmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:53:02.377245+00:00
-- url     : https://prove2.me/theorems/18b86988-e388-47bb-bb0c-1c1888450c87
-- title:
--   Quantum Channel: map is Symmetric
-- statement:
--   The Quantum Channel construction uses the map is Symmetric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/TraceNorm.lean#L32-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/TraceNorm.lean#L32-L37

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

theorem QEC.Semantics.QuantumChannel.map_isSymmetric (Phi : QuantumChannel H K) {A : Operator H}
    (hA : A.IsSymmetric) : (Phi A).IsSymmetric := by sorry
