-- Prove2me | Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_measure
-- name    : QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_measure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:54:10.220402+00:00
-- url     : https://prove2.me/theorems/594598e1-016f-4e90-b818-d2d4403205ec
-- title:
--   Adaptive Program: eval measure
-- statement:
--   The Adaptive Program construction uses the eval measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/AdaptiveIdealClifford.lean#L533-L543
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/AdaptiveIdealClifford.lean#L533-L543

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

theorem QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_measure
    (measurement : JointMeasurement ι κ)
    (next : JointSyndrome κ → AdaptiveProgram κ Token presentation)
    (rho : DensityOperator (QubitRegister ι)) :
    (measure measurement next).eval rho =
      Finset.univ.1.bind fun syndrome =>
        if hpositive : 0 < (measurement.branch syndrome rho).weight then
          ((next syndrome).eval (measurement.conditionalDensity syndrome rho hpositive)).map
            (TerminalBranch.prependSyndrome measurement syndrome rho hpositive)
        else 0 := by sorry

attribute [defeq] QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_measure
