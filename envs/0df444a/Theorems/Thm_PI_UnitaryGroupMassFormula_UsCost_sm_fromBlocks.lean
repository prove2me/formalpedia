-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_sm_fromBlocks
-- name    : PI.UnitaryGroupMassFormula.UsCost.sm_fromBlocks
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:52:02.65655+00:00
-- url     : https://prove2.me/theorems/4089798c-f3e5-473b-aff8-7e8b48d48750
-- title:
--   Us Cost: sm from Blocks
-- statement:
--   The Us Cost construction uses the sm from Blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Smooth.lean#L67-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Smooth.lean#L67-L76

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

theorem PI.UnitaryGroupMassFormula.UsCost.sm_fromBlocks {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    {A : X → Matrix ι κ ℂ} {B : X → Matrix ι κ' ℂ} {C : X → Matrix ι' κ ℂ} {D : X → Matrix ι' κ' ℂ}
    (hA : ContDiffAt ℝ n A x₀) (hB : ContDiffAt ℝ n B x₀) (hC : ContDiffAt ℝ n C x₀) (hD : ContDiffAt ℝ n D x₀) :
    ContDiffAt ℝ n (fun x => Matrix.fromBlocks (A x) (B x) (C x) (D x)) x₀ := by sorry
