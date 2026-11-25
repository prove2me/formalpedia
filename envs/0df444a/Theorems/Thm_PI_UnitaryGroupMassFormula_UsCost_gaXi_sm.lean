-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_gaXi_sm
-- name    : PI.UnitaryGroupMassFormula.UsCost.gaXi_sm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:42:37.0988+00:00
-- url     : https://prove2.me/theorems/d1bc8583-2017-5bb3-b691-5ced3bab951a
-- title:
--   Us Cost: ga Xi sm
-- statement:
--   The Us Cost construction uses the ga Xi sm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Smooth.lean#L183-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Smooth.lean#L183-L187

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
variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ}

theorem PI.UnitaryGroupMassFormula.UsCost.gaXi_sm (hd : ∀ i, d i ≠ 0) (ξ : Xi k p s ρ σ) (γ : B.Mat k ρ) {Z : G.Mat s} (hZ : G.detM Z ≠ 0) :
    ContDiffAt ℝ n (fun Z' : G.Mat s => gaXi k ρ σ d ξ Z' γ) Z := by sorry
