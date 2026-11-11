-- Prove2me | Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_coin_totalWeight
-- name    : QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_coin_totalWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:58:05.9292+00:00
-- url     : https://prove2.me/theorems/9ddd0fcb-3098-4593-bd2f-6e6e8912306e
-- title:
--   Adaptive Program: eval coin total Weight
-- statement:
--   The evaluator equation for a fair Boolean coin.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/AdaptiveIdealClifford.lean#L613-L629
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/AdaptiveIdealClifford.lean#L613-L629

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

theorem QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_coin_totalWeight
    (next : Bool → AdaptiveProgram κ Token presentation)
    (rho : DensityOperator (QubitRegister ι)) :
    totalWeight ((coin next).eval rho) =
      (1 / 2 : ℝ) * totalWeight ((next false).eval rho) +
        (1 / 2 : ℝ) * totalWeight ((next true).eval rho) := by sorry
