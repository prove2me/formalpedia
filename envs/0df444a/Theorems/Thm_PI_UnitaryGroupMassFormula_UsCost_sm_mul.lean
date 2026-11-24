-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_sm_mul
-- name    : PI.UnitaryGroupMassFormula.UsCost.sm_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:17:17.920121+00:00
-- url     : https://prove2.me/theorems/757d781e-b5bb-4edd-9682-1a5c2525b4bf
-- title:
--   Us Cost: sm mul
-- statement:
--   The Us Cost construction uses the sm mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Smooth.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Smooth.lean#L22-L27

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_Smooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x₀ : X}

theorem PI.UnitaryGroupMassFormula.UsCost.sm_mul {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ] {F : X → Matrix ι κ ℂ} {G : X → Matrix κ μ ℂ}
    (hF : ContDiffAt ℝ n F x₀) (hG : ContDiffAt ℝ n G x₀) : ContDiffAt ℝ n (fun x => F x * G x) x₀ := by sorry
