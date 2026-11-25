-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ratioVd_nonneg
-- name    : ReciprocityTheory.ChartRestriction.DS.ratioVd_nonneg
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:10:17.568067+00:00
-- url     : https://prove2.me/theorems/3f06d1d0-3e6e-5639-8567-68e4ee29b7cc
-- title:
--   DS: ratio Vd nonneg
-- statement:
--   The DS construction uses the ratio Vd nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L195-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Residue.lean#L195-L217

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.ratioVd_nonneg {μ : Fin n → ℝ} (hμ : Function.Injective μ) (hint : ∀ a b, ∃ m : ℤ, μ a - μ b = (m : ℝ))
    (s : Fin n) : 0 ≤ ratioVd μ s ∧ (ratioVd μ s = 0 ↔ ¬ Function.Injective (μ - Pi.single s 1)) := by sorry
