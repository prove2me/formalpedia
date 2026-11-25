-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_trunc_bdd_5a2b401ede64
-- name    : P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_trunc_bdd_5a2b401ede64
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:00:48.555526+00:00
-- url     : https://prove2.me/theorems/82347672-0814-5581-9643-b50fe182400b
-- title:
--   P2 M Ground Theory Heights  Heights Regular Trunc Transfer trunc bdd 5a2b401ede64: P2 M Ground Theory Heights  Heights Regular Trunc Transfer trunc bdd 5a2b401ede64
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Trunc Transfer trunc bdd 5a2b401ede64 construction uses the P2 M Ground Theory Heights  Heights Regular Trunc Transfer trunc bdd 5a2b401ede64 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PTruncTransfer.lean#L52-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PTruncTransfer.lean#L52-L72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncTransfer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PTruncTransfer
import Theorems.Thm_ReciprocityTheory_AnForm_A_PlurisubharmonicExtension_trunc_bdd

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

theorem P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_trunc_bdd_5a2b401ede64 (k : Fin R.N) : ∃ c > 0, ∃ M : ℝ, ∀ K : ℝ, ∀ x ∈ R.mid k, ∀ s ≤ c,
    ∀ y ∈ closedBall (R.chart k x) s, R.trunc K k y ≤ max M (-K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«TruncTransfer».«trunc_bdd» := P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_trunc_bdd_5a2b401ede64
