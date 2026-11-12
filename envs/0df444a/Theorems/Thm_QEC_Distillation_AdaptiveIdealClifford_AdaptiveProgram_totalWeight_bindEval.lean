-- Prove2me | Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_totalWeight_bindEval
-- name    : QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.totalWeight_bindEval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T13:52:35.077407+00:00
-- url     : https://prove2.me/theorems/732bd082-405d-4bbf-b4b3-e7fe12256062
-- title:
--   Adaptive Program: total Weight bind Eval
-- statement:
--   If every selected continuation is normalized, finite bind preserves total
--   weight.  Together with `eval_totalWeight_eq_one`, this is the sequential
--   product-weight normalization law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/AdaptiveIdealClifford.lean#L754-L773
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/AdaptiveIdealClifford.lean#L754-L773

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

theorem QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.totalWeight_bindEval
    (branches : Multiset (TerminalBranch (ι := ι) (κ := κ) (Token := Token)))
    (next : TerminalBranch (ι := ι) (κ := κ) (Token := Token) →
      AdaptiveProgram κ Token presentation)
    (hnormal : ∀ first, totalWeight ((next first).eval first.output) = 1) :
    totalWeight (bindEval branches next) = totalWeight branches := by sorry
