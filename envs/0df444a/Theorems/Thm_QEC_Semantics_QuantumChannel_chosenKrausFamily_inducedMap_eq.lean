-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumChannel_chosenKrausFamily_inducedMap_eq
-- name    : QEC.Semantics.QuantumChannel.chosenKrausFamily_inducedMap_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:51:38.305938+00:00
-- url     : https://prove2.me/theorems/1aa9a7ce-2af2-4101-8ac6-6e367c3a432b
-- title:
--   Quantum Channel: chosen Kraus Family induced Map eq
-- statement:
--   The chosen finite Choi--Kraus family induces exactly the channel map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Instrument.lean#L49-L51
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Instrument.lean#L49-L51

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

theorem QEC.Semantics.QuantumChannel.chosenKrausFamily_inducedMap_eq (Φ : QuantumChannel H K) :
    (Φ.chosenKrausFamily).inducedMap = Φ.toLinearMap := by sorry
