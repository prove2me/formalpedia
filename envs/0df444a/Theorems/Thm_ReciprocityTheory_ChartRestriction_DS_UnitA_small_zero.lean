-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_small_zero
-- name    : ReciprocityTheory.ChartRestriction.DS.UnitA.small_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:45:22.901144+00:00
-- url     : https://prove2.me/theorems/6be4fcc5-9dbc-5fd1-9784-e373b6420b9d
-- title:
--   Unit A: small zero
-- statement:
--   The Unit A construction uses the small zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/UnitarizeA.lean#L203-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/UnitarizeA.lean#L203-L216

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_UnitarizeA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.UnitA
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] (μ : Measure G)
variable {μ}
variable [μ.IsMulRightInvariant] [SFinite μ]

theorem ReciprocityTheory.ChartRestriction.DS.UnitA.small_zero {D : ℂ} {C : ℝ} (h : ∀ t : ℝ, 0 < t → t ≤ 1 → ‖D‖ ≤ t * C) : D = 0 := by sorry
