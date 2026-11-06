-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_quantumChannelTensorPower_comp_mapDensity_product
-- name    : QEC.Semantics.FiniteInstrument.quantumChannelTensorPower_comp_mapDensity_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:03:36.580242+00:00
-- url     : https://prove2.me/theorems/da751482-11d7-47d9-b798-c857f2e73d77
-- title:
--   Finite Instrument: quantum Channel Tensor Power comp map Density product
-- statement:
--   On a genuine recursive product input, composing two tensor-power channels
--   is exactly the tensor power of the one-factor channel composition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ChannelProductFunctorial.lean#L59-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ChannelProductFunctorial.lean#L59-L78

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

theorem QEC.Semantics.FiniteInstrument.quantumChannelTensorPower_comp_mapDensity_product
    (first : QuantumChannel H K) (second : QuantumChannel K L)
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0))
    (sigmaUnit : DensityOperator (tensorPowerCarrier K 0))
    (tauUnit : DensityOperator (tensorPowerCarrier L 0))
    (hsigma : sigmaUnit.toOperator = rhoUnit.toOperator)
    (htau : tauUnit.toOperator = sigmaUnit.toOperator)
    (attempts : Nat) :
    (quantumChannelTensorPower second attempts).mapDensity
        ((quantumChannelTensorPower first attempts).mapDensity
          (tensorPowerProductInput rho rhoUnit attempts)) =
      tensorPowerProductInput
        ((QuantumChannel.comp second first).mapDensity rho)
        tauUnit attempts := by sorry
