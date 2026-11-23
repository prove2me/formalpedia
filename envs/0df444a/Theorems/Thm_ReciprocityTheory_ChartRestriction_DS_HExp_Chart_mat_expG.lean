-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_Chart_mat_expG
-- name    : ReciprocityTheory.ChartRestriction.DS.HExp.Chart.mat_expG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:44.174048+00:00
-- url     : https://prove2.me/theorems/227e54e3-537e-4e65-b2ff-5aa9ee04d0d4
-- title:
--   Chart: mat exp G
-- statement:
--   The Chart construction uses the mat exp G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/HaarExpB.lean#L151-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/FormalDegree/HaarVolumes/HaarExpB.lean#L151-L151

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HExp
open MeasureTheory Filter Topology Metric NormedSpace Set
open scoped ENNReal NNReal
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
open ReciprocityTheory.ChartRestriction.DS.HExp.Chart
variable {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G] (C : Chart V G)

theorem ReciprocityTheory.ChartRestriction.DS.HExp.Chart.mat_expG (X : V) : C.mat (C.expG X) = exp (X : 𝔸) := by sorry
