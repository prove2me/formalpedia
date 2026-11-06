-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumChannel_toFiniteInstrument_complete
-- name    : QEC.Semantics.QuantumChannel.toFiniteInstrument_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:49:14.391422+00:00
-- url     : https://prove2.me/theorems/5a322009-d77f-473a-bb73-0d4dd1bb58ac
-- title:
--   Quantum Channel: to Finite Instrument complete
-- statement:
--   The unit-observed chosen-Kraus instrument is complete.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Instrument.lean#L71-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Instrument.lean#L71-L73

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

theorem QEC.Semantics.QuantumChannel.toFiniteInstrument_complete (Φ : QuantumChannel H K) :
    (Φ.toFiniteInstrument).kraus.Complete := by sorry
