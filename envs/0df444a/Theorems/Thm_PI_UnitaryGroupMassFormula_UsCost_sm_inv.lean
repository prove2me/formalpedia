-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_sm_inv
-- name    : PI.UnitaryGroupMassFormula.UsCost.sm_inv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:36:48.296263+00:00
-- url     : https://prove2.me/theorems/80168e0f-b299-5560-a9b9-f9482e024ad2
-- title:
--   Us Cost: sm inv
-- statement:
--   The Us Cost construction uses the sm inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Smooth.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Smooth.lean#L60-L65

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

theorem PI.UnitaryGroupMassFormula.UsCost.sm_inv {ι : Type*} [Fintype ι] [DecidableEq ι] {F : X → Matrix ι ι ℂ} (hF : ContDiffAt ℝ n F x₀)
    (hu : (F x₀).det ≠ 0) : ContDiffAt ℝ n (fun x => (F x)⁻¹) x₀ := by sorry
