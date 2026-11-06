-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerRejectedCount_succ
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerRejectedCount_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:56:34.582448+00:00
-- url     : https://prove2.me/theorems/416092b8-0e72-4de4-9453-675f7cdf3662
-- title:
--   Finite Instrument: tensor Power Rejected Count succ
-- statement:
--   The finite rejection count adds exactly the new non-accepted outcome at a
--   successor trial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/FirstMoment.lean#L69-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/FirstMoment.lean#L69-L83

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_FirstMoment
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerRejectedCount_succ {Ω : Type w} [Fintype Ω]
    (accepts : Ω → Prop) [DecidablePred accepts] (attempts : Nat)
    (head : Ω) (tail : tensorPowerHistory Ω attempts) :
    tensorPowerRejectedCount accepts (attempts + 1) (head, tail) =
      (if accepts head then 0 else 1) +
        tensorPowerRejectedCount accepts attempts tail := by sorry
