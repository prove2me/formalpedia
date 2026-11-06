-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_quantumChannelTensorPower_rankOne_basis
-- name    : QEC.Semantics.FiniteInstrument.quantumChannelTensorPower_rankOne_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:03:46.39421+00:00
-- url     : https://prove2.me/theorems/13066767-a655-4d88-9adc-1a8cb063e4ba
-- title:
--   Finite Instrument: quantum Channel Tensor Power rank One basis
-- statement:
--   If one channel sends computational matrix units to scalar multiples of
--   computational matrix units, its homogeneous tensor power does the same with
--   the product of the actual per-coordinate scalars.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ChannelProductFunctorial.lean#L182-L264
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ChannelProductFunctorial.lean#L182-L264

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProduct
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProductFunctorial
set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
open scoped BigOperators TensorProduct
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L]
  [FiniteQuantumSystem L]

theorem QEC.Semantics.FiniteInstrument.quantumChannelTensorPower_rankOne_basis
    {beta gamma : Type u} [Fintype beta] [Fintype gamma]
    (channel : QuantumChannel H K)
    (sourceBasis : OrthonormalBasis beta Complex H)
    (targetBasis : OrthonormalBasis gamma Complex K)
    (mapIndex : beta → gamma)
    (coefficient : beta → beta → Complex)
    (haction : ∀ left right,
      channel
          (InnerProductSpace.rankOne Complex
            (sourceBasis left) (sourceBasis right)).toLinearMap =
        coefficient left right •
          (InnerProductSpace.rankOne Complex
            (targetBasis (mapIndex left))
            (targetBasis (mapIndex right))).toLinearMap) :
    ∀ attempts
      (left right : tensorPowerHistory beta attempts),
      quantumChannelTensorPower channel attempts
          (InnerProductSpace.rankOne Complex
            (tensorPowerBasis sourceBasis attempts left)
            (tensorPowerBasis sourceBasis attempts right)).toLinearMap =
        (∏ trial : Fin attempts,
          coefficient
            (tensorPowerHistoryAt beta attempts left trial)
            (tensorPowerHistoryAt beta attempts right trial)) •
          (InnerProductSpace.rankOne Complex
            (tensorPowerBasis targetBasis attempts
              (tensorPowerHistoryMap mapIndex attempts left))
            (tensorPowerBasis targetBasis attempts
              (tensorPowerHistoryMap mapIndex attempts right))).toLinearMap := by sorry
