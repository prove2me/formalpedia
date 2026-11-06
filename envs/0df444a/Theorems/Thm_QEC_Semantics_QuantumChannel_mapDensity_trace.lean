-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumChannel_mapDensity_trace
-- name    : QEC.Semantics.QuantumChannel.mapDensity_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:50:34.230142+00:00
-- url     : https://prove2.me/theorems/2b7842ca-47cd-4f98-bcca-acf07d40febe
-- title:
--   Quantum Channel: map Density trace
-- statement:
--   The Quantum Channel construction uses the map Density trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Core.lean#L166-L169
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Core.lean#L166-L169

import Definitions.Def_QEC_Semantics_Core_Definitions
import Definitions.Def_QEC_Semantics_Channels_Core
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct
open QEC.Semantics.QuantumChannel
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem QEC.Semantics.QuantumChannel.mapDensity_trace (Φ : QuantumChannel H K)
    (rho : DensityOperator H) :
    LinearMap.trace Complex K (Φ.mapDensity rho).toOperator = 1 := by sorry
