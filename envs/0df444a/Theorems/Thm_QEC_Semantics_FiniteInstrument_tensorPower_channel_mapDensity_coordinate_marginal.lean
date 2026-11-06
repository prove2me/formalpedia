-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_channel_mapDensity_coordinate_marginal
-- name    : QEC.Semantics.FiniteInstrument.tensorPower_channel_mapDensity_coordinate_marginal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:00:58.103207+00:00
-- url     : https://prove2.me/theorems/727ebe28-071d-4af2-9d6b-2a9c26dd6016
-- title:
--   Finite Instrument: tensor Power channel map Density coordinate marginal
-- statement:
--   A homogeneous tensor channel maps every true coordinate marginal by its
--   one-factor channel, even when the tensor-power input is correlated.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalChannel.lean#L397-L445
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalChannel.lean#L397-L445

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalBornMass
import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_complete

set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {kappaTwo : Type x} [Fintype kappaTwo]
variable {Xi : Type y} [Fintype Xi]
variable {H K R S : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup R] [InnerProductSpace Complex R] [FiniteQuantumSystem R]
variable [NormedAddCommGroup S] [InnerProductSpace Complex S] [FiniteQuantumSystem S]

theorem QEC.Semantics.FiniteInstrument.tensorPower_channel_mapDensity_coordinate_marginal
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete) :
    ∀ (attempts : Nat)
      (rho : DensityOperator (tensorPowerCarrier H attempts))
      (trial : Fin attempts),
      tensorPowerInputMarginal attempts
          (((I.tensorPower attempts).kraus.toQuantumChannel
            (I.tensorPower_complete hI attempts)).mapDensity rho) trial =
        (I.kraus.toQuantumChannel hI).mapDensity
          (tensorPowerInputMarginal attempts rho trial) := by sorry
