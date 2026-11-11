-- Prove2me | Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_JointMeasurement_branch_weight
-- name    : QEC.Distillation.AdaptiveIdealClifford.JointMeasurement.branch_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:52:55.073092+00:00
-- url     : https://prove2.me/theorems/d5f6e98b-423d-4080-9a37-8b5da6f21cfd
-- title:
--   Joint Measurement: branch weight
-- statement:
--   The Joint Measurement construction uses the branch weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/AdaptiveIdealClifford.lean#L283-L286
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/AdaptiveIdealClifford.lean#L283-L286

import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
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

theorem QEC.Distillation.AdaptiveIdealClifford.JointMeasurement.branch_weight (measurement : JointMeasurement ι κ)
    (syndrome : JointSyndrome κ) (rho : DensityOperator (QubitRegister ι)) :
    (measurement.branch syndrome rho).weight = measurement.instrument.bornWeight syndrome rho := by sorry

attribute [defeq] QEC.Distillation.AdaptiveIdealClifford.JointMeasurement.branch_weight
