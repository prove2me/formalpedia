-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_pair_b614e5fd0ac9
-- name    : P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_pair_b614e5fd0ac9
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:18:36.386393+00:00
-- url     : https://prove2.me/theorems/db69c97f-df14-5c93-9221-94a5afd242a0
-- title:
--   P2 M Ground Theory Heights  Heights Regular Trunc Transfer pair b614e5fd0ac9: P2 M Ground Theory Heights  Heights Regular Trunc Transfer pair b614e5fd0ac9
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Trunc Transfer pair b614e5fd0ac9 construction uses the P2 M Ground Theory Heights  Heights Regular Trunc Transfer pair b614e5fd0ac9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PTruncTransfer.lean#L74-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PTruncTransfer.lean#L74-L180

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

theorem P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_pair_b614e5fd0ac9 (j k : Fin R.N) : ∃ δ₀ > 0, ∃ c₀ > 0, ∃ L₀ B₀ : ℝ, ∀ δ L B : ℝ, δ ≤ δ₀ → L * δ ≤ c₀ →
    2 * L₀ ≤ L → 1 ≤ L → B₀ ≤ B →
    ∀ K : ℝ, ∀ x ∈ R.mid j ∩ R.mid k, ∀ t : ℝ, 0 < t → t < δ → ∀ y ∈ closedBall (R.chart j x) t,
      R.trunc K j y ≤ max (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B) +
        (R.q j (R.chart j x) - R.q k (R.chart k x)) + L * t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«TruncTransfer».«pair» := P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_pair_b614e5fd0ac9
