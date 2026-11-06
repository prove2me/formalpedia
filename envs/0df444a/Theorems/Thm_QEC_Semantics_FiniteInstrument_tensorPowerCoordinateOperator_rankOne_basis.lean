-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerCoordinateOperator_rankOne_basis
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerCoordinateOperator_rankOne_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:21:25.903597+00:00
-- url     : https://prove2.me/theorems/7a4c3040-c850-41a5-b698-62fa2c2a24d3
-- title:
--   Finite Instrument: tensor Power Coordinate Operator rank One basis
-- statement:
--   On a computational matrix unit, selecting one recursive tensor coordinate
--   retains that coordinate's matrix unit and contracts every discarded
--   coordinate by its exact computational-basis inner product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/Marginal.lean#L200-L267
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/Marginal.lean#L200-L267

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerCoordinateOperator_rankOne_basis
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H]
    {beta : Type u} [Fintype beta]
    (basis : OrthonormalBasis beta Complex H) :
    forall (attempts : Nat) (trial : Fin attempts)
      (left right : tensorPowerHistory beta attempts),
      tensorPowerCoordinateOperator attempts trial
          (InnerProductSpace.rankOne Complex
            (tensorPowerBasis basis attempts left)
            (tensorPowerBasis basis attempts right)).toLinearMap =
        (∏ coordinate : Fin attempts,
            if coordinate = trial then 1
            else inner Complex
              (basis (tensorPowerHistoryAt beta attempts right coordinate))
              (basis (tensorPowerHistoryAt beta attempts left coordinate))) •
          (InnerProductSpace.rankOne Complex
            (basis (tensorPowerHistoryAt beta attempts left trial))
            (basis (tensorPowerHistoryAt beta attempts right trial))).toLinearMap := by sorry
