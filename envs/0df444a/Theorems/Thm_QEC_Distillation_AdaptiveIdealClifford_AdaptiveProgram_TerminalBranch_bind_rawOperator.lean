-- Prove2me | Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_TerminalBranch_bind_rawOperator
-- name    : QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.TerminalBranch.bind_rawOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:52:27.503049+00:00
-- url     : https://prove2.me/theorems/a04f173b-beed-4a03-834a-df63d481884b
-- title:
--   Terminal Branch: bind raw Operator
-- statement:
--   The raw branch operator after binding is weighted by the first branch mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/AdaptiveIdealClifford.lean#L724-L734
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/AdaptiveIdealClifford.lean#L724-L734

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
open QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {Wire : Type} [Fintype Wire] {Token : Type}
variable {presentation : CliffordPresentation (H := QubitRegister ι) Wire}

theorem QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.TerminalBranch.bind_rawOperator
    (first second : TerminalBranch (ι := ι) (κ := κ) (Token := Token)) :
    (first.bind second).rawOperator =
      (first.weight : Complex) • second.rawOperator := by sorry
