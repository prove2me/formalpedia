-- Prove2me | Theorems.Thm_PI_SwSandwichOfWork_SideB_pick
-- name    : PI.SwSandwichOfWork.SideB_pick
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:33:01.247948+00:00
-- url     : https://prove2.me/theorems/00780970-2bb8-54e1-8a58-51000e5077cb
-- title:
--   Sw Sandwich Of Work: Side B pick
-- statement:
--   The Sw Sandwich Of Work construction uses the Side B pick property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SandwichChart/SideBUnrealifyRL.lean#L44-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SandwichChart/SideBUnrealifyRL.lean#L44-L61

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_SwSand
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SandwichOfOfCharts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SideBUnrealifyRL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology Classical
open scoped ENNReal NNReal
open PI PI.SwSandwichOfWork
open PI.SwBig PI.SwSand
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
variable {k r : ℕ}

theorem PI.SwSandwichOfWork.SideB_pick (S : Set (Mat k r)) (T : Submodule ℝ (Mat k r)) (hST : lieE S = T.map RL) (x : Mt k r)
    (h : rhoS k r S x ≠ ⊤) (τ : ℝ) (hτ : 0 < τ) :
    ∃ X ∈ T, NormedSpace.exp X = Matrix.of x ∧ ‖RL X‖ ^ 2 < (rhoS k r S x).toReal ^ 2 + τ := by sorry
