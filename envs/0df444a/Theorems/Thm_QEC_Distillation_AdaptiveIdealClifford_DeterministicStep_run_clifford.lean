-- Prove2me | Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_DeterministicStep_run_clifford
-- name    : QEC.Distillation.AdaptiveIdealClifford.DeterministicStep.run_clifford
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:53:19.959448+00:00
-- url     : https://prove2.me/theorems/89df811a-5ac3-43a3-8115-bb38bb2c0600
-- title:
--   Deterministic Step: run clifford
-- statement:
--   The Deterministic Step construction uses the run clifford property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/AdaptiveIdealClifford.lean#L364-L368
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/AdaptiveIdealClifford.lean#L364-L368

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
open QEC.Distillation.AdaptiveIdealClifford.DeterministicStep
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {Wire : Type} [Fintype Wire] {Token : Type}
variable {presentation : CliffordPresentation (H := QubitRegister ι) Wire}

theorem QEC.Distillation.AdaptiveIdealClifford.DeterministicStep.run_clifford (gate : CliffordSyntax presentation)
    (rho : DensityOperator (QubitRegister ι)) :
    (DeterministicStep.clifford (Token := Token) gate).run rho =
      gate.channel.mapDensity rho := by sorry

attribute [defeq] QEC.Distillation.AdaptiveIdealClifford.DeterministicStep.run_clifford
