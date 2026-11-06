-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitBitstringEquiv_apply
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerQubitBitstringEquiv_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:49:14.838627+00:00
-- url     : https://prove2.me/theorems/1ad4ddb9-7af6-4bee-a16f-1b9f263d3c4c
-- title:
--   Finite Instrument: tensor Power Qubit Bitstring Equiv apply
-- statement:
--   The flattened label evaluates at a trial/local-coordinate pair by reading
--   the corresponding value from the recursive history.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/Basis.lean#L67-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/Basis.lean#L67-L73

import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
open scoped TensorProduct
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable {β : Type v} [Fintype β]

theorem QEC.Semantics.FiniteInstrument.tensorPowerQubitBitstringEquiv_apply
    (ι : Type u) [Fintype ι] (attempts : Nat)
    (history : tensorPowerHistory (Qubit.Bitstring ι) attempts)
    (trial : Fin attempts) (coordinate : ι) :
    tensorPowerQubitBitstringEquiv ι attempts history (trial, coordinate) =
      tensorPowerHistoryAt (Qubit.Bitstring ι) attempts history trial coordinate := by sorry

attribute [defeq] QEC.Semantics.FiniteInstrument.tensorPowerQubitBitstringEquiv_apply
