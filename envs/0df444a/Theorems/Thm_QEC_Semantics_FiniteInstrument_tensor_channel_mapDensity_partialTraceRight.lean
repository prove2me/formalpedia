-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_channel_mapDensity_partialTraceRight
-- name    : QEC.Semantics.FiniteInstrument.tensor_channel_mapDensity_partialTraceRight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:21:17.320851+00:00
-- url     : https://prove2.me/theorems/990d3a47-3fd9-4c20-b882-020d3c21a884
-- title:
--   Finite Instrument: tensor channel map Density partial Trace Right
-- statement:
--   Density-operator form of `tensor_inducedMap_partialTraceRight`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalChannel.lean#L212-L226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalChannel.lean#L212-L226

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

theorem QEC.Semantics.FiniteInstrument.tensor_channel_mapDensity_partialTraceRight
    (I : FiniteInstrument kappa Omega H K)
    (J : FiniteInstrument kappaTwo Xi R S)
    (hI : I.kraus.Complete) (hJ : J.kraus.Complete)
    (rho : DensityOperator (CompositeSystem H R)) :
    partialTraceRightRaw_mapDensity K S
        (((I.tensor J).kraus.toQuantumChannel
          (I.tensor_complete J hI hJ)).mapDensity rho) =
      (I.kraus.toQuantumChannel hI).mapDensity
        (partialTraceRightRaw_mapDensity H R rho) := by sorry
