-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_bornWeight_fst_sum_eq_partialTraceRight
-- name    : QEC.Semantics.FiniteInstrument.tensor_bornWeight_fst_sum_eq_partialTraceRight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:20:51.981546+00:00
-- url     : https://prove2.me/theorems/bac4d11d-8873-4512-a136-c29557bada2f
-- title:
--   Finite Instrument: tensor born Weight fst sum eq partial Trace Right
-- statement:
--   Summing every visible right-factor outcome of a tensor instrument gives
--   the left visible Born mass on the true partial-trace marginal.  No product
--   input or independence premise is used.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalBornMass.lean#L148-L189
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Tensor/MarginalBornMass.lean#L148-L189

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

theorem QEC.Semantics.FiniteInstrument.tensor_bornWeight_fst_sum_eq_partialTraceRight
    (I : FiniteInstrument kappa Omega H K)
    (J : FiniteInstrument kappaTwo Xi R S) (hJ : J.kraus.Complete)
    (leftOutcome : Omega) (rho : DensityOperator (CompositeSystem H R)) :
    (∑ rightOutcome : Xi,
      (I.tensor J).bornWeight (leftOutcome, rightOutcome) rho) =
      I.bornWeight leftOutcome (partialTraceRightRaw_mapDensity H R rho) := by sorry
