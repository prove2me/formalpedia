-- Prove2me | Theorems.Thm_PI_Residue_fib_le
-- name    : PI.Residue.fib_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:19:39.203839+00:00
-- url     : https://prove2.me/theorems/c071614a-27fa-42de-be61-5b74f012c274
-- title:
--   Residue: fib le
-- statement:
--   The Residue construction uses the fib le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/BUnfold.lean#L71-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/BUnfold.lean#L71-L105

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_BUnfold
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped nonZeroDivisors ENNReal Classical Pointwise
noncomputable section
open PI PI.Residue
variable {K : Type} [Field K] [NumberField K]

theorem PI.Residue.fib_le (hUP : UnitPreserving) (ρ : ℝ) (x1 : mixedSpace K) :
    ∑' g : (𝓞 K)ˣ ⧸ torsion K, Fv ρ (urep g • x1) ≤
      volume ({y | 1 / 2 < mixedEmbedding.norm y} ∩ hit K ρ x1) := by sorry
