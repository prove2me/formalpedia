-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_fixedDensityReplacementSwap_apply_tmul
-- name    : QEC.Semantics.FiniteInstrument.fixedDensityReplacementSwap_apply_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:50:47.18859+00:00
-- url     : https://prove2.me/theorems/322f4e28-8770-4354-9f40-7f82aa7e6f4f
-- title:
--   Finite Instrument: fixed Density Replacement Swap apply tmul
-- statement:
--   The replacement commutation unitary exchanges pure tensor factors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ConditionedChannel.lean#L37-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ConditionedChannel.lean#L37-L42

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

theorem QEC.Semantics.FiniteInstrument.fixedDensityReplacementSwap_apply_tmul (H K : Type)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (h : H) (k : K) :
    fixedDensityReplacementSwap H K (h ⊗ₜ[Complex] k) = k ⊗ₜ[Complex] h := by sorry

attribute [defeq] QEC.Semantics.FiniteInstrument.fixedDensityReplacementSwap_apply_tmul
