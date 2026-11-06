-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_quantumChannelTensorPower_mapDensity_productInput
-- name    : QEC.Semantics.FiniteInstrument.quantumChannelTensorPower_mapDensity_productInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:01:13.0712+00:00
-- url     : https://prove2.me/theorems/fd6b0671-88d7-4d5e-b1ae-df3507501266
-- title:
--   Finite Instrument: quantum Channel Tensor Power map Density product Input
-- statement:
--   The actual channel obtained from a homogeneous tensor power maps a
--   recursive product density factorwise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ChannelProduct.lean#L79-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ChannelProduct.lean#L79-L117

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProduct
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_complete
import Theorems.Thm_QEC_Semantics_QuantumChannel_toFiniteInstrument_complete

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

theorem QEC.Semantics.FiniteInstrument.quantumChannelTensorPower_mapDensity_productInput
    (channel : QuantumChannel H K)
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0))
    (sigmaUnit : DensityOperator (tensorPowerCarrier K 0))
    (hunit : sigmaUnit.toOperator = rhoUnit.toOperator)
    (attempts : Nat) :
    ((((channel.toFiniteInstrument).tensorPower attempts).kraus.toQuantumChannel
          ((channel.toFiniteInstrument).tensorPower_complete
            channel.toFiniteInstrument_complete attempts)).mapDensity
        (tensorPowerProductInput rho rhoUnit attempts)).toOperator =
      (tensorPowerProductInput (channel.mapDensity rho) sigmaUnit attempts).toOperator := by sorry
