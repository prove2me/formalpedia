-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerShortage_rejectedCount_lower_bound
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerShortage_rejectedCount_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:56:20.410204+00:00
-- url     : https://prove2.me/theorems/39b5215f-ea6d-4d21-8bb5-548314ab0d2f
-- title:
--   Finite Instrument: tensor Power Shortage rejected Count lower bound
-- statement:
--   A history short of `required` accepted trials has at least
--   `attempts - required + 1` actual rejections.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/FirstMoment.lean#L46-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/FirstMoment.lean#L46-L52

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_FirstMoment
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerShortage_rejectedCount_lower_bound {Ω : Type w} [Fintype Ω]
    (accepts : Ω → Prop) [DecidablePred accepts] (attempts required : Nat)
    (history : tensorPowerHistory Ω attempts) (hrequired : required ≤ attempts)
    (hshort : (tensorPowerAcceptedIndices accepts attempts history).card < required) :
    attempts - required + 1 ≤ tensorPowerRejectedCount accepts attempts history := by sorry
