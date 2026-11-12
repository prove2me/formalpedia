-- Prove2me | Theorems.Thm_QEC_Distillation_AdaptiveIdealClifford_AdaptiveProgram_eval_measure_totalWeight
-- name    : QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_measure_totalWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:03:52.833202+00:00
-- url     : https://prove2.me/theorems/93c078ed-dd8a-416f-9f8f-5c1e97f4d221
-- title:
--   Adaptive Program: eval measure total Weight
-- statement:
--   The evaluator equation for one finite joint-syndrome measurement.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/AdaptiveIdealClifford.lean#L632-L660
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/AdaptiveIdealClifford.lean#L632-L660

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

theorem QEC.Distillation.AdaptiveIdealClifford.AdaptiveProgram.eval_measure_totalWeight
    (measurement : JointMeasurement ι κ)
    (next : JointSyndrome κ → AdaptiveProgram κ Token presentation)
    (rho : DensityOperator (QubitRegister ι)) :
    totalWeight ((measure measurement next).eval rho) =
      ∑ syndrome, if hpositive : 0 < (measurement.branch syndrome rho).weight then
        (measurement.branch syndrome rho).weight *
          totalWeight ((next syndrome).eval
            (measurement.conditionalDensity syndrome rho hpositive))
      else 0 := by sorry
