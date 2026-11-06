-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerRegisterTrialChannel_rankOne_basis
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerRegisterTrialChannel_rankOne_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:00:58.674454+00:00
-- url     : https://prove2.me/theorems/c826a9a0-22c1-40e9-ae7c-10cf3026197a
-- title:
--   Finite Instrument: tensor Power Register Trial Channel rank One basis
-- statement:
--   On a flattened computational matrix unit, selecting one complete trial
--   retains exactly that trial's register matrix unit and contracts all other
--   trial blocks by their literal computational-basis inner products.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/Marginal.lean#L344-L384
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Registers/Marginal.lean#L344-L384

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerRegisterTrialChannel_rankOne_basis
    (iota : Type u) [Fintype iota] [DecidableEq iota]
    (attempts : Nat) (trial : Fin attempts)
    (left right : Qubit.Bitstring (Fin attempts × iota)) :
    tensorPowerRegisterTrialChannel iota attempts trial
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun
            (Qubit.Bitstring (Fin attempts × iota)) Complex left)
          (EuclideanSpace.basisFun
            (Qubit.Bitstring (Fin attempts × iota)) Complex right)).toLinearMap =
      (∏ coordinate : Fin attempts,
          if coordinate = trial then 1
          else inner Complex
            (EuclideanSpace.basisFun (Qubit.Bitstring iota) Complex
              (fun site => right (coordinate, site)))
            (EuclideanSpace.basisFun (Qubit.Bitstring iota) Complex
              (fun site => left (coordinate, site)))) •
        (InnerProductSpace.rankOne Complex
          (EuclideanSpace.basisFun (Qubit.Bitstring iota) Complex
            (fun site => left (trial, site)))
          (EuclideanSpace.basisFun (Qubit.Bitstring iota) Complex
            (fun site => right (trial, site)))).toLinearMap := by sorry
