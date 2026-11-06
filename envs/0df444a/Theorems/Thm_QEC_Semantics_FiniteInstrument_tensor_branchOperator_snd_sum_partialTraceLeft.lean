-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensor_branchOperator_snd_sum_partialTraceLeft
-- name    : QEC.Semantics.FiniteInstrument.tensor_branchOperator_snd_sum_partialTraceLeft
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:22:13.573138+00:00
-- url     : https://prove2.me/theorems/101f659e-bbe1-434f-91cb-88d752047c38
-- title:
--   Finite Instrument: tensor branch Operator snd sum partial Trace Left
-- statement:
--   Summing every left observed outcome and tracing out its output leaves the
--   selected right branch on the true right input marginal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/MarginalBranchOperator.lean#L209-L221
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/MarginalBranchOperator.lean#L209-L221

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

theorem QEC.Semantics.FiniteInstrument.tensor_branchOperator_snd_sum_partialTraceLeft
    (I : FiniteInstrument kappa Omega H K) (hI : I.kraus.Complete)
    (J : FiniteInstrument kappaTwo Xi R S)
    (outcome : Xi) (A : Operator (CompositeSystem H R)) :
    FiniteMatrixEntropy.partialTraceLeftRaw K S
        (∑ leftOutcome : Omega,
          (I.tensor J).branchOperator (leftOutcome, outcome) A) =
      J.branchOperator outcome
        (FiniteMatrixEntropy.partialTraceLeftRaw H R A) := by sorry
