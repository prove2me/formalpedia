-- Prove2me | Theorems.Thm_PI_Residue_lattice_sum_le_shell_volume
-- name    : PI.Residue.lattice_sum_le_shell_volume
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:19:50.575886+00:00
-- url     : https://prove2.me/theorems/240d3e17-e502-5fe4-aab7-ee514e9eb4f1
-- title:
--   Residue: lattice sum le shell volume
-- statement:
--   The Residue construction uses the lattice sum le shell volume property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/BUnfold.lean#L137-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/BUnfold.lean#L137-L148

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

theorem PI.Residue.lattice_sum_le_shell_volume (hUP : UnitPreserving) (J : (Ideal (𝓞 K))⁰) (ρ : ℝ) :
    ∑' x : lat K J, Fv ρ (x : mixedSpace K) ≤
      volume (shell K) +
        ∑' x : idealSet K J,
          volume ({y | 1 / 2 < mixedEmbedding.norm y} ∩ hit K ρ (x : mixedSpace K)) := by sorry
