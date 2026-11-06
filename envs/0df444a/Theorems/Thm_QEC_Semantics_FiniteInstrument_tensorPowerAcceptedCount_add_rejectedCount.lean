-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerAcceptedCount_add_rejectedCount
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerAcceptedCount_add_rejectedCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:05:26.944194+00:00
-- url     : https://prove2.me/theorems/6207e72f-fe44-4461-a0e9-740843744ed8
-- title:
--   Finite Instrument: tensor Power Accepted Count add rejected Count
-- statement:
--   The actual accepted and rejected trial counts partition the finite retry
--   history.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/FirstMoment.lean#L30-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/FirstMoment.lean#L30-L42

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_FirstMoment
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerAcceptedCount_add_rejectedCount {Ω : Type w} [Fintype Ω]
    (accepts : Ω → Prop) [DecidablePred accepts] (attempts : Nat)
    (history : tensorPowerHistory Ω attempts) :
    (tensorPowerAcceptedIndices accepts attempts history).card +
      tensorPowerRejectedCount accepts attempts history = attempts := by sorry
