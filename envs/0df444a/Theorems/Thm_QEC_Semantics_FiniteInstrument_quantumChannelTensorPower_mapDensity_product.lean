-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_quantumChannelTensorPower_mapDensity_product
-- name    : QEC.Semantics.FiniteInstrument.quantumChannelTensorPower_mapDensity_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:02:25.828553+00:00
-- url     : https://prove2.me/theorems/f2e0cd7b-4ede-4c31-aa9f-c49c507202f3
-- title:
--   Finite Instrument: quantum Channel Tensor Power map Density product
-- statement:
--   A tensor-power channel maps a genuine recursive product density
--   factorwise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ChannelProductFunctorial.lean#L44-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ChannelProductFunctorial.lean#L44-L55

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

theorem QEC.Semantics.FiniteInstrument.quantumChannelTensorPower_mapDensity_product
    (channel : QuantumChannel H K)
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0))
    (sigmaUnit : DensityOperator (tensorPowerCarrier K 0))
    (hunit : sigmaUnit.toOperator = rhoUnit.toOperator)
    (attempts : Nat) :
    (quantumChannelTensorPower channel attempts).mapDensity
        (tensorPowerProductInput rho rhoUnit attempts) =
      tensorPowerProductInput (channel.mapDensity rho) sigmaUnit attempts := by sorry
