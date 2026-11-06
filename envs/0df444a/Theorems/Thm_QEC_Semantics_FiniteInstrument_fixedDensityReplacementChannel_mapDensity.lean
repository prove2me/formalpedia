-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_fixedDensityReplacementChannel_mapDensity
-- name    : QEC.Semantics.FiniteInstrument.fixedDensityReplacementChannel_mapDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:34:05.14892+00:00
-- url     : https://prove2.me/theorems/aeab47c4-1892-4bbf-9a02-35789ccfd4ee
-- title:
--   Finite Instrument: fixed Density Replacement Channel map Density
-- statement:
--   The physical replacement channel sends every normalized density input to
--   the supplied normalized replacement density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ConditionedChannel.lean#L81-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ConditionedChannel.lean#L81-L114

import Definitions.Def_QEC_Semantics_Instruments_Selection_SelectedSubsystem
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedChannel
set_option autoImplicit false
universe v w
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.fixedDensityReplacementChannel_mapDensity (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (sigma : DensityOperator K) (rho : DensityOperator H) :
    (fixedDensityReplacementChannel H K sigma).mapDensity rho = sigma := by sorry
