-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_isCompact_chart_image_aa5560298c9d
-- name    : P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_isCompact_chart_image_aa5560298c9d
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:36.932864+00:00
-- url     : https://prove2.me/theorems/39d91e07-cf61-48c2-a4e4-4319b0cf9334
-- title:
--   P2 M Ground Theory Heights  Heights Regular Trunc Transfer is Compact chart image aa5560298c9d: P2 M Ground Theory Heights  Heights Regular Trunc Transfer is Compact chart image aa5560298c9d
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Trunc Transfer is Compact chart image aa5560298c9d construction uses the P2 M Ground Theory Heights  Heights Regular Trunc Transfer is Compact chart image aa5560298c9d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PTruncTransfer.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PTruncTransfer.lean#L48-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncTransfer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PTruncTransfer
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
open Metric Filter Topology Set
open ReciprocityTheory.AnForm.A (coordDiv limsupExt polyMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.TruncTransfer
variable {D : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X] {A : FinHolAtlas D X}
  (R : RegChartData A)

theorem P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_isCompact_chart_image_aa5560298c9d (j : Fin R.N) {s : Set X} (hs : s ⊆ closure (R.mid j))
    (hsc : IsClosed s) : IsCompact (R.chart j '' s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«TruncTransfer».«isCompact_chart_image» := P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_isCompact_chart_image_aa5560298c9d
