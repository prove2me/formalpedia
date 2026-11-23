-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_UnitA_pr_smul_left
-- name    : ReciprocityTheory.ChartRestriction.DS.UnitA.pr_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:38.426541+00:00
-- url     : https://prove2.me/theorems/d76ab560-1ab4-42f9-b7f6-2f716216120a
-- title:
--   Unit A: pr smul left
-- statement:
--   The Unit A construction uses the pr smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/UnitarizeA.lean#L97-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/UnitarizeA.lean#L97-L103

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

theorem ReciprocityTheory.ChartRestriction.DS.UnitA.pr_smul_left (c : ℂ) (a b : G → ℂ) : pr μ (c • a) b = star c * pr μ a b := by sorry
