-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_sm_fromCols
-- name    : PI.UnitaryGroupMassFormula.UsCost.sm_fromCols
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:50:35.573037+00:00
-- url     : https://prove2.me/theorems/e55f4a46-9927-435e-9215-1b5ae9dbfae9
-- title:
--   Us Cost: sm from Cols
-- statement:
--   The Us Cost construction uses the sm from Cols property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Smooth.lean#L86-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Smooth.lean#L86-L92

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

theorem PI.UnitaryGroupMassFormula.UsCost.sm_fromCols {ι κ κ' : Type*} [Fintype ι] [Fintype κ] [Fintype κ']
    {A : X → Matrix ι κ ℂ} {B : X → Matrix ι κ' ℂ} (hA : ContDiffAt ℝ n A x₀) (hB : ContDiffAt ℝ n B x₀) :
    ContDiffAt ℝ n (fun x => Matrix.fromCols (A x) (B x)) x₀ := by sorry
