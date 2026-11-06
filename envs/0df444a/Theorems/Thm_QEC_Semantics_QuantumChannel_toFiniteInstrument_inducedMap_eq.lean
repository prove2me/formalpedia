-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumChannel_toFiniteInstrument_inducedMap_eq
-- name    : QEC.Semantics.QuantumChannel.toFiniteInstrument_inducedMap_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:49:45.774473+00:00
-- url     : https://prove2.me/theorems/6c426f8d-7eb8-4ed6-9d82-93a3736ad383
-- title:
--   Quantum Channel: to Finite Instrument induced Map eq
-- statement:
--   The induced map of the unit-observed instrument is exactly the channel map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Instrument.lean#L76-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Instrument.lean#L76-L78

import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Definitions.Def_QEC_Semantics_Instruments_Sequential_DependentComposition
import Definitions.Def_QEC_Semantics_Channels_Instrument
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.QuantumChannel
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem QEC.Semantics.QuantumChannel.toFiniteInstrument_inducedMap_eq (Φ : QuantumChannel H K) :
    (Φ.toFiniteInstrument).kraus.inducedMap = Φ.toLinearMap := by sorry
