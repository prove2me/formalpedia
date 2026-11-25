-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_mem_multiIndicesBelow_iff
-- name    : ReciprocityTheory.ChartRestriction.G.AR.mem_multiIndicesBelow_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:27:36.012455+00:00
-- url     : https://prove2.me/theorems/6c957eb3-ecda-49a0-bbc0-6352efef91c1
-- title:
--   AR: mem multi Indices Below iff
-- statement:
--   The AR construction uses the mem multi Indices Below iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/PointwiseNormConstantSection.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/PointwiseNormConstantSection.lean#L16-L17

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_IndependentSectionsUpperCount
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_TaylorExpansionLocalCoordinates
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_PointwiseNormConstantSection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR
open MeasureTheory Filter Topology Asymptotics ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal
noncomputable section
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type*} [AddCommGroup La] (A : WeightedAtlas n Y ι La)

theorem ReciprocityTheory.ChartRestriction.G.AR.mem_multiIndicesBelow_iff {a0 : ℕ} {α : Fin n → ℕ} : α ∈ multiLt n a0 ↔ ∑ k, α k < a0 := by sorry
