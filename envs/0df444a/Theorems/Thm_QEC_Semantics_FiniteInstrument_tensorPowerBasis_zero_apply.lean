-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBasis_zero_apply
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerBasis_zero_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:48:38.379701+00:00
-- url     : https://prove2.me/theorems/af963912-93de-4e52-a93b-5154050676e3
-- title:
--   Finite Instrument: tensor Power Basis zero apply
-- statement:
--   The zero-level tensor-power basis uses the unique basis index of the
--   literal one-dimensional tensor unit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/Basis.lean#L38-L45
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/Basis.lean#L38-L45

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

theorem QEC.Semantics.FiniteInstrument.tensorPowerBasis_zero_apply (b : OrthonormalBasis β Complex H)
    (index : PUnit) :
    tensorPowerBasis b 0 index =
      EuclideanSpace.basisFun (ULift.{u} (Fin 1)) Complex
        ((Equiv.ofUnique (ULift.{u} (Fin 1)) PUnit).symm index) := by sorry
