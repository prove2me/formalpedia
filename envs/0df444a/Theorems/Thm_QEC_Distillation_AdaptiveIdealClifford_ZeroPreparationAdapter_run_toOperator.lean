-- Prove2me | Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_ZeroPreparationAdapter_run_toOperator
-- name    : QEC.Distillation.AdaptiveIdealClifford.ZeroPreparationAdapter.run_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:52:14.027432+00:00
-- url     : https://prove2.me/theorems/faad32c6-0f9f-4ba5-bcc3-19538ad8d39d
-- title:
--   Zero Preparation Adapter: run to Operator
-- statement:
--   The Zero Preparation Adapter construction uses the run to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/AdaptiveIdealClifford.lean#L239-L243
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/AdaptiveIdealClifford.lean#L239-L243

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
open QEC.Distillation.AdaptiveIdealClifford.ZeroPreparationAdapter
variable {H K : Type}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem QEC.Distillation.AdaptiveIdealClifford.ZeroPreparationAdapter.run_toOperator (adapter : ZeroPreparationAdapter (H := H) (K := K))
    (rho : DensityOperator H) :
    (adapter.run rho).toOperator =
      adapter.consumer (DensityOperator.tensorDensity rho zeroQubitDensity).toOperator := by sorry

attribute [defeq] QEC.Distillation.AdaptiveIdealClifford.ZeroPreparationAdapter.run_toOperator
