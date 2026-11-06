-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumChannel_chosenKrausFamily_representation
-- name    : QEC.Semantics.QuantumChannel.chosenKrausFamily_representation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:49:41.22229+00:00
-- url     : https://prove2.me/theorems/598de54e-8510-4b7e-be02-ae3a4c78c1e2
-- title:
--   Quantum Channel: chosen Kraus Family representation
-- statement:
--   The chosen family is complete and has exactly the channel's operator map.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Instrument.lean#L37-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Instrument.lean#L37-L41

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

theorem QEC.Semantics.QuantumChannel.chosenKrausFamily_representation (Φ : QuantumChannel H K) :
    (Φ.chosenKrausFamily).Complete ∧
      (Φ.chosenKrausFamily).inducedMap = Φ.toLinearMap := by sorry
