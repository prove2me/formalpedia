-- Prove2me | Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_JointMeasurement_sum_branch_weight_eq_one
-- name    : QEC.Distillation.AdaptiveIdealClifford.JointMeasurement.sum_branch_weight_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:03:49.394021+00:00
-- url     : https://prove2.me/theorems/9aa284de-4f41-4fc2-9bd4-dc21698c24ec
-- title:
--   Joint Measurement: sum branch weight eq one
-- statement:
--   The Joint Measurement construction uses the sum branch weight eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/AdaptiveIdealClifford.lean#L293-L297
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/AdaptiveIdealClifford.lean#L293-L297

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

theorem QEC.Distillation.AdaptiveIdealClifford.JointMeasurement.sum_branch_weight_eq_one (measurement : JointMeasurement ι κ)
    (rho : DensityOperator (QubitRegister ι)) :
    ∑ syndrome, (measurement.branch syndrome rho).weight = 1 := by sorry
