-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_Mink_exists_small_mem_ideal
-- name    : ReciprocityTheory.ChartRestriction.G.TB.Mink.exists_small_mem_ideal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:40:32.1082+00:00
-- url     : https://prove2.me/theorems/3ee6daa5-5c68-553a-9f0c-4cfd6b114891
-- title:
--   Mink: exists small mem ideal
-- statement:
--   The Mink construction uses the exists small mem ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/ExistsSmallMemIdeal.lean#L14-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/ExistsSmallMemIdeal.lean#L14-L67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExistsSmallMemIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.Mink
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory ENNReal Module
open scoped nonZeroDivisors
variable (K : Type) [Field K] [NumberField K]

theorem ReciprocityTheory.ChartRestriction.G.TB.Mink.exists_small_mem_ideal (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ∃ a : 𝓞 K, a ∈ I ∧ a ≠ 0 ∧ ∀ w : InfinitePlace K,
      w (a : K) < 3 * ((Ideal.absNorm I : ℝ) * Real.sqrt |(discr K : ℝ)|) ^ ((finrank ℚ K : ℝ)⁻¹) := by sorry
