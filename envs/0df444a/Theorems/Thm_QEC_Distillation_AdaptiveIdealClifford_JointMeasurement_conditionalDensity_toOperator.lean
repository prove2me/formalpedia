-- Prove2me | Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_JointMeasurement_conditionalDensity_toOperator
-- name    : QEC.Distillation.AdaptiveIdealClifford.JointMeasurement.conditionalDensity_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:53:12.938749+00:00
-- url     : https://prove2.me/theorems/a74512f1-9cfb-4791-9131-1f74fe4f72e0
-- title:
--   Joint Measurement: conditional Density to Operator
-- statement:
--   The Joint Measurement construction uses the conditional Density to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/AdaptiveIdealClifford.lean#L306-L312
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/AdaptiveIdealClifford.lean#L306-L312

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Theorems.Thm_QEC_Semantics_FiniteInstrument_conditionalDensity_toOperator
attribute [local simp] QEC.Semantics.FiniteInstrument.conditionalDensity_toOperator


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.AdaptiveIdealClifford
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open scoped TensorProduct
universe u v w
variable {H K R E : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]
variable [NormedAddCommGroup R] [InnerProductSpace Complex R]
  [FiniteQuantumSystem R]
variable [NormedAddCommGroup E] [InnerProductSpace Complex E]
  [FiniteQuantumSystem E]
open QEC.Distillation.AdaptiveIdealClifford.JointMeasurement
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]

theorem QEC.Distillation.AdaptiveIdealClifford.JointMeasurement.conditionalDensity_toOperator (measurement : JointMeasurement ι κ)
    (syndrome : JointSyndrome κ) (rho : DensityOperator (QubitRegister ι))
    (hpositive : 0 < (measurement.branch syndrome rho).weight) :
    (measurement.conditionalDensity syndrome rho hpositive).toOperator =
      ((measurement.branch syndrome rho).weight : Complex)⁻¹ •
        (measurement.branch syndrome rho).operator := by sorry
