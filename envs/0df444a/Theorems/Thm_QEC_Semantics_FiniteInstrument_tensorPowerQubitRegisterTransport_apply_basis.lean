-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitRegisterTransport_apply_basis
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerQubitRegisterTransport_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:49:26.091852+00:00
-- url     : https://prove2.me/theorems/1691570a-e8db-4fe4-b35a-8189a2eee60d
-- title:
--   Finite Instrument: tensor Power Qubit Register Transport apply basis
-- statement:
--   The flattened transport sends every recursive computational basis vector
--   to the computational basis vector labelled by the history/coordinate curry
--   equivalence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/Basis.lean#L93-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/Basis.lean#L93-L102

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

theorem QEC.Semantics.FiniteInstrument.tensorPowerQubitRegisterTransport_apply_basis
    (ι : Type u) [Fintype ι] [DecidableEq ι] (attempts : Nat)
    (history : tensorPowerHistory (Qubit.Bitstring ι) attempts) :
    tensorPowerQubitRegisterTransport ι attempts
      (tensorPowerBasis (EuclideanSpace.basisFun (Qubit.Bitstring ι) Complex)
        attempts history) =
      EuclideanSpace.basisFun (Qubit.Bitstring (Fin attempts × ι)) Complex
        (tensorPowerQubitBitstringEquiv ι attempts history) := by sorry
