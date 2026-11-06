-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumChannel_chosenKrausFamily_complete
-- name    : QEC.Semantics.QuantumChannel.chosenKrausFamily_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:52:04.944327+00:00
-- url     : https://prove2.me/theorems/beae6693-73e6-44c3-b690-dc8417dba724
-- title:
--   Quantum Channel: chosen Kraus Family complete
-- statement:
--   Completeness of the chosen finite Choi--Kraus family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Instrument.lean#L44-L46
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Instrument.lean#L44-L46

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

theorem QEC.Semantics.QuantumChannel.chosenKrausFamily_complete (Φ : QuantumChannel H K) :
    (Φ.chosenKrausFamily).Complete := by sorry
