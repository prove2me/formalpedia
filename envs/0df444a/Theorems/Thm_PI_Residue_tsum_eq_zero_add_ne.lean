-- Prove2me | Theorems.Thm_PI_Residue_tsum_eq_zero_add_ne
-- name    : PI.Residue.tsum_eq_zero_add_ne
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:20:03.333837+00:00
-- url     : https://prove2.me/theorems/55de9ed4-a2b0-4ca0-a26b-46d257c8c311
-- title:
--   Residue: tsum eq zero add ne
-- statement:
--   The Residue construction uses the tsum eq zero add ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/BUnfold.lean#L125-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ResidueLatticeCount/BUnfold.lean#L125-L132

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

theorem PI.Residue.tsum_eq_zero_add_ne {α : Type*} [Zero α] (f : α → ℝ≥0∞) :
    ∑' x, f x = f 0 + ∑' x : {x : α // x ≠ 0}, f x := by sorry
