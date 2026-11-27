-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_TB_Mink_exists_small_mem_ideal__e7daf5da2ddb
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_TB_Mink_exists_small_mem_ideal__e7daf5da2ddb
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:43:26.244221+00:00
-- url     : https://prove2.me/theorems/df70b5d4-269f-50e4-807b-624d8384a923
-- title:
--   P2 M Reciprocity Theory Chart Restriction G TB Mink exists small mem ideal  e7daf5da2ddb: P2 M Reciprocity Theory Chart Restriction G TB Mink exists small mem ideal  e7daf5da2ddb
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G TB Mink exists small mem ideal  e7daf5da2ddb construction uses the P2 M Reciprocity Theory Chart Restriction G TB Mink exists small mem ideal  e7daf5da2ddb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/ExistsSmallMemIdeal.lean#L69-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/ExistsSmallMemIdeal.lean#L69-L73

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

theorem P2M_ReciprocityTheory_ChartRestriction_G_TB_Mink_exists_small_mem_ideal__e7daf5da2ddb (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ∃ a : 𝓞 K, a ∈ I ∧ a ≠ 0 ∧ ∀ σ : K →+* ℂ,
      ‖σ (a : K)‖ < 3 * ((Ideal.absNorm I : ℝ) * Real.sqrt |(discr K : ℝ)|) ^ ((finrank ℚ K : ℝ)⁻¹) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«TB».«Mink».«exists_small_mem_ideal'» := P2M_ReciprocityTheory_ChartRestriction_G_TB_Mink_exists_small_mem_ideal__e7daf5da2ddb
