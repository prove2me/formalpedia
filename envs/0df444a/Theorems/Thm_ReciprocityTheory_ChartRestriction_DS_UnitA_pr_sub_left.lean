-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_pr_sub_left
-- name    : ReciprocityTheory.ChartRestriction.DS.UnitA.pr_sub_left
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:45:24.577334+00:00
-- url     : https://prove2.me/theorems/68faa1e9-abc1-501f-93a3-ed7ff5e71279
-- title:
--   Unit A: pr sub left
-- statement:
--   The Unit A construction uses the pr sub left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/UnitarizeA.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/UnitarizeA.lean#L50-L56

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

theorem ReciprocityTheory.ChartRestriction.DS.UnitA.pr_sub_left {a a₁ b : G → ℂ} (ha : MemLp a 2 μ) (ha₁ : MemLp a₁ 2 μ) (hb : MemLp b 2 μ) :
    pr μ (fun x => a x - a₁ x) b = pr μ a b - pr μ a₁ b := by sorry
