-- Prove2me | Theorems.Thm_QEC_Semantics_QuantumChannel_toFiniteInstrument_sum_bornWeight_eq_one
-- name    : QEC.Semantics.QuantumChannel.toFiniteInstrument_sum_bornWeight_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:57:47.320921+00:00
-- url     : https://prove2.me/theorems/7d81048c-4e01-43a9-945a-c2e246c82c7f
-- title:
--   Quantum Channel: to Finite Instrument sum born Weight eq one
-- statement:
--   The sole observed outcome has normalized total Born mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Instrument.lean#L87-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Channels/Instrument.lean#L87-L90

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

theorem QEC.Semantics.QuantumChannel.toFiniteInstrument_sum_bornWeight_eq_one (Φ : QuantumChannel H K)
    (rho : DensityOperator H) :
    ∑ outcome, (Φ.toFiniteInstrument).bornWeight outcome rho = 1 := by sorry
