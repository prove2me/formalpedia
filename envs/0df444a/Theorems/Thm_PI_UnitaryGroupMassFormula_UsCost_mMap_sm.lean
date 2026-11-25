-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_mMap_sm
-- name    : PI.UnitaryGroupMassFormula.UsCost.mMap_sm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:36:54.14631+00:00
-- url     : https://prove2.me/theorems/6adcad57-7885-57dc-abed-9940bbb969c0
-- title:
--   Us Cost: m Map sm
-- statement:
--   The Us Cost construction uses the m Map sm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Smooth.lean#L113-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Smooth.lean#L113-L120

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

theorem PI.UnitaryGroupMassFormula.UsCost.mMap_sm {k j ρ : ℕ} {M : X → Matrix (Fin j) (Fin j) ℂ} (hM : ContDiffAt ℝ n M x₀)
    (hdet : (M x₀).det ≠ 0) (γ : B.Mat k ρ) : ContDiffAt ℝ n (fun x => mMap k j ρ (M x) γ) x₀ := by sorry
