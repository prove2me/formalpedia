-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_exists_lipschitz_near_3535e800fccc
-- name    : P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_exists_lipschitz_near_3535e800fccc
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:19:36.373796+00:00
-- url     : https://prove2.me/theorems/330d8b89-9ed8-4233-ac5d-b61d502d7187
-- title:
--   P2 M Ground Theory Heights  Heights Regular Trunc Transfer exists lipschitz near 3535e800fccc: P2 M Ground Theory Heights  Heights Regular Trunc Transfer exists lipschitz near 3535e800fccc
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular Trunc Transfer exists lipschitz near 3535e800fccc construction uses the P2 M Ground Theory Heights  Heights Regular Trunc Transfer exists lipschitz near 3535e800fccc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PTruncTransfer.lean#L16-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PTruncTransfer.lean#L16-L31

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

theorem P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_exists_lipschitz_near_3535e800fccc {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {W K : Set E} (hW : IsOpen W)
    (hK : IsCompact K) (hKW : K ⊆ W) (hf : ∀ y ∈ W, ContDiffAt ℝ 1 f y) :
    ∃ ε > 0, ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, closedBall z ε ⊆ W ∧
      ∀ y ∈ closedBall z ε, ‖f y - f z‖ ≤ C * ‖y - z‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«TruncTransfer».«exists_lipschitz_near» := P2M_GroundTheory_Heights__Heights_Regular_TruncTransfer_exists_lipschitz_near_3535e800fccc
