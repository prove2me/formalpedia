-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_branchOperator_fst_sum_partialTraceRight
-- name    : QEC.Semantics.FiniteInstrument.tensor_branchOperator_fst_sum_partialTraceRight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:21:41.474482+00:00
-- url     : https://prove2.me/theorems/738cb801-3b6c-4ae7-acb8-af51b440ad35
-- title:
--   Finite Instrument: tensor branch Operator fst sum partial Trace Right
-- statement:
--   Summing every right observed outcome and tracing out its output leaves the
--   selected left branch on the true left input marginal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/MarginalBranchOperator.lean#L194-L205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/MarginalBranchOperator.lean#L194-L205

import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalChannel
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_MarginalBranchOperator
set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators
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

theorem QEC.Semantics.FiniteInstrument.tensor_branchOperator_fst_sum_partialTraceRight
    (I : FiniteInstrument kappa Omega H K)
    (J : FiniteInstrument kappaTwo Xi R S) (hJ : J.kraus.Complete)
    (outcome : Omega) (A : Operator (CompositeSystem H R)) :
    partialTraceRightRaw K S
        (∑ rightOutcome : Xi,
          (I.tensor J).branchOperator (outcome, rightOutcome) A) =
      I.branchOperator outcome (partialTraceRightRaw H R A) := by sorry
