-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_channel_mapDensity_leftMarginal
-- name    : QEC.Semantics.FiniteInstrument.tensor_channel_mapDensity_leftMarginal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:21:24.420534+00:00
-- url     : https://prove2.me/theorems/cd68dadc-b028-4030-9600-1227de6e5f50
-- title:
--   Finite Instrument: tensor channel map Density left Marginal
-- statement:
--   Density-operator form of `tensor_inducedMap_partialTraceLeft`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalChannel.lean#L378-L393
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalChannel.lean#L378-L393

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalBornMass
import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_complete

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

theorem QEC.Semantics.FiniteInstrument.tensor_channel_mapDensity_leftMarginal
    (I : FiniteInstrument kappa Omega H K)
    (J : FiniteInstrument kappaTwo Xi R S)
    (hI : I.kraus.Complete) (hJ : J.kraus.Complete)
    (rho : DensityOperator (CompositeSystem H R)) :
    DensityOperator.leftMarginal
        (((I.tensor J).kraus.toQuantumChannel
          (I.tensor_complete J hI hJ)).mapDensity rho) =
      (J.kraus.toQuantumChannel hJ).mapDensity
        (DensityOperator.leftMarginal rho) := by sorry
