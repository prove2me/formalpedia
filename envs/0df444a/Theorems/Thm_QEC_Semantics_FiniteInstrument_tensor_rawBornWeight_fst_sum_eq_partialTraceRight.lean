-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_rawBornWeight_fst_sum_eq_partialTraceRight
-- name    : QEC.Semantics.FiniteInstrument.tensor_rawBornWeight_fst_sum_eq_partialTraceRight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:20:51.984737+00:00
-- url     : https://prove2.me/theorems/730b0e0a-0f46-4180-8428-408a1afed3ad
-- title:
--   Finite Instrument: tensor raw Born Weight fst sum eq partial Trace Right
-- statement:
--   Summing the raw branches of a complete instrument on the right tensor
--   factor leaves the left raw branch evaluated on the actual right-partial-trace
--   marginal.  The bipartite input may be correlated.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalBornMass.lean#L59-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalBornMass.lean#L59-L143

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalBornMass
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

theorem QEC.Semantics.FiniteInstrument.tensor_rawBornWeight_fst_sum_eq_partialTraceRight
    (I : FiniteInstrument kappa Omega H K)
    (J : FiniteInstrument kappaTwo Xi R S) (hJ : J.kraus.Complete)
    (leftIndex : kappa) (rho : DensityOperator (CompositeSystem H R)) :
    (∑ rightIndex : kappaTwo,
      (I.tensor J).rawBornWeight (leftIndex, rightIndex) rho) =
      I.rawBornWeight leftIndex (partialTraceRightRaw_mapDensity H R rho) := by sorry
