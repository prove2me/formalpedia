-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerHistory_punit_eq
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerHistory_punit_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:56:57.004464+00:00
-- url     : https://prove2.me/theorems/9cd6bb8c-74c0-4de3-b002-a4537369bc25
-- title:
--   Finite Instrument: tensor Power History punit eq
-- statement:
--   A recursive history with one possible visible outcome is the canonical
--   constant history.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ChannelProduct.lean#L32-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ChannelProduct.lean#L32-L45

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProduct
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
open scoped TensorProduct
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]

theorem QEC.Semantics.FiniteInstrument.tensorPowerHistory_punit_eq :
    ∀ (attempts : Nat) (history : tensorPowerHistory PUnit attempts),
      history = tensorPowerHistoryOf PUnit attempts (fun _ => PUnit.unit) := by sorry
