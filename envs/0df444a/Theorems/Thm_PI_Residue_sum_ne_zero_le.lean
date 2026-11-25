-- Prove2me | Theorems.Thm_PI_Residue_sum_ne_zero_le
-- name    : PI.Residue.sum_ne_zero_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:20:21.657232+00:00
-- url     : https://prove2.me/theorems/28636264-6898-4118-8e2a-39e9db4e4509
-- title:
--   Residue: sum ne zero le
-- statement:
--   The Residue construction uses the sum ne zero le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/BUnfold.lean#L107-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/BUnfold.lean#L107-L123

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

theorem PI.Residue.sum_ne_zero_le (J : (Ideal (𝓞 K))⁰) (F : mixedSpace K → ℝ≥0∞) :
    ∑' x : {x : lat K J // x ≠ 0}, F ((x : lat K J) : mixedSpace K) ≤
      ∑' p : idealSet K J × ((𝓞 K)ˣ ⧸ torsion K), F (urep p.2 • (p.1 : mixedSpace K)) := by sorry
