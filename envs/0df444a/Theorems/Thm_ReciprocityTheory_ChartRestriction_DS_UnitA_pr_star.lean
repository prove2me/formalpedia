-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_pr_star
-- name    : ReciprocityTheory.ChartRestriction.DS.UnitA.pr_star
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:44.257574+00:00
-- url     : https://prove2.me/theorems/02a399c2-a840-42f9-bef3-7d34c7d9b4d7
-- title:
--   Unit A: pr star
-- statement:
--   The Unit A construction uses the pr star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/UnitarizeA.lean#L40-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/UnitarizeA.lean#L40-L48

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

theorem ReciprocityTheory.ChartRestriction.DS.UnitA.pr_star (a b : G → ℂ) : star (pr μ a b) = pr μ b a := by sorry
