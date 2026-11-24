-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_isCompact_image_closure_mid_4db7e722a909
-- name    : P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_isCompact_image_closure_mid_4db7e722a909
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:48.215571+00:00
-- url     : https://prove2.me/theorems/c51fd921-97be-49e7-a067-726e82a2f44e
-- title:
--   P2 M Ground Theory Heights  Heights Regular Potential Charts is Compact image closure mid 4db7e722a909: P2 M Ground Theory Heights  Heights Regular Potential Charts is Compact image closure mid 4db7e7
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Potential Charts is Compact image closure mid 4db7e722a909 construction uses the P2 M Ground Theory Heights  Heights Regular Potential Charts is Compact image closure mid 4db7e722a909 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsCompactImageClosureMid.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsCompactImageClosureMid.lean#L38-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_BoundedStatements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsCompactImageClosureMid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli shrink regMax tmax)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open ReciprocityTheory.AnForm (levi)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.PotentialCharts
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (P : PotentialCharts A)

theorem P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_isCompact_image_closure_mid_4db7e722a909 [CompactSpace X] (j : Fin P.N) :
    IsCompact ((P.chart j) '' closure (P.mid j)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«PotentialCharts».«isCompact_image_closure_mid» := P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_isCompact_image_closure_mid_4db7e722a909
