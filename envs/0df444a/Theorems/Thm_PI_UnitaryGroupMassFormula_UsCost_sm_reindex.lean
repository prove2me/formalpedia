-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_sm_reindex
-- name    : PI.UnitaryGroupMassFormula.UsCost.sm_reindex
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:52:54.930424+00:00
-- url     : https://prove2.me/theorems/cb1dfa0f-1079-4f72-818f-de26c7c015a3
-- title:
--   Us Cost: sm reindex
-- statement:
--   The Us Cost construction uses the sm reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Smooth.lean#L94-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Smooth.lean#L94-L99

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

theorem PI.UnitaryGroupMassFormula.UsCost.sm_reindex {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
    (e₁ : ι ≃ ι') (e₂ : κ ≃ κ') {F : X → Matrix ι κ ℂ} (hF : ContDiffAt ℝ n F x₀) :
    ContDiffAt ℝ n (fun x => Matrix.reindex e₁ e₂ (F x)) x₀ := by sorry
