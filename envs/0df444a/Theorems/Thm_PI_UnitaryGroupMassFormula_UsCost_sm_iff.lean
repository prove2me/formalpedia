-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_sm_iff
-- name    : PI.UnitaryGroupMassFormula.UsCost.sm_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:28:35.684721+00:00
-- url     : https://prove2.me/theorems/d6910fe5-5e71-45c6-91a1-584f1a68b461
-- title:
--   Us Cost: sm iff
-- statement:
--   The Us Cost construction uses the sm iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Smooth.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Smooth.lean#L18-L20

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

theorem PI.UnitaryGroupMassFormula.UsCost.sm_iff {ι κ : Type*} [Fintype ι] [Fintype κ] {F : X → Matrix ι κ ℂ} :
    ContDiffAt ℝ n F x₀ ↔ ∀ i j, ContDiffAt ℝ n (fun x => F x i j) x₀ := by sorry
