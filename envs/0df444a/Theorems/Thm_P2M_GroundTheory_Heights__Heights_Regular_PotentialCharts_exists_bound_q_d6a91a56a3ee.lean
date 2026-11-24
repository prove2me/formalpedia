-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_exists_bound_q_d6a91a56a3ee
-- name    : P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_exists_bound_q_d6a91a56a3ee
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:51.805455+00:00
-- url     : https://prove2.me/theorems/7cc71ee5-b07b-451c-9d29-9c266111a6f2
-- title:
--   P2 M Ground Theory Heights  Heights Regular Potential Charts exists bound q d6a91a56a3ee: P2 M Ground Theory Heights  Heights Regular Potential Charts exists bound q d6a91a56a3ee
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Potential Charts exists bound q d6a91a56a3ee construction uses the P2 M Ground Theory Heights  Heights Regular Potential Charts exists bound q d6a91a56a3ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsCompactImageClosureMid.lean#L56-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsCompactImageClosureMid.lean#L56-L67

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

theorem P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_exists_bound_q_d6a91a56a3ee [CompactSpace X] {δ : ℝ}
    (hδ : ∀ j, cthickening δ ((P.chart j) '' closure (P.mid j)) ⊆ (P.chart j).target) :
    ∃ Q : ℝ, ∀ j, ∀ y ∈ cthickening δ ((P.chart j) '' closure (P.mid j)), |P.q j y| ≤ Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«PotentialCharts».«exists_bound_q» := P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_exists_bound_q_d6a91a56a3ee
