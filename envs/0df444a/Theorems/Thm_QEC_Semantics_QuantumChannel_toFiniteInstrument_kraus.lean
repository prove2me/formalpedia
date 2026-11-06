-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumChannel_toFiniteInstrument_kraus
-- name    : QEC.Semantics.QuantumChannel.toFiniteInstrument_kraus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:57:43.104758+00:00
-- url     : https://prove2.me/theorems/13ef3919-72b9-4ba3-8056-5c05645eb9b9
-- title:
--   Quantum Channel: to Finite Instrument kraus
-- statement:
--   The raw family of the unit-observed instrument is the chosen Choi--Kraus family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Instrument.lean#L66-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Instrument.lean#L66-L68

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

theorem QEC.Semantics.QuantumChannel.toFiniteInstrument_kraus (Φ : QuantumChannel H K) :
    (Φ.toFiniteInstrument).kraus = Φ.chosenKrausFamily := by sorry
