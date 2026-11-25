-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SegrePartition_contDiff_segreSqSum_2a999fd991c8
-- name    : P2M_GroundTheory_Heights__Heights_SegrePartition_contDiff_segreSqSum_2a999fd991c8
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:37:24.079207+00:00
-- url     : https://prove2.me/theorems/df3857a7-8041-5d8c-b133-ce8d3bbbcba5
-- title:
--   P2 M Ground Theory Heights  Heights Segre Partition cont Diff segre Sq Sum 2a999fd991c8: P2 M Ground Theory Heights  Heights Segre Partition cont Diff segre Sq Sum 2a999fd991c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Segre Partition cont Diff segre Sq Sum 2a999fd991c8 construction uses the P2 M Ground Theory Heights  Heights Segre Partition cont Diff segre Sq Sum 2a999fd991c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegrePartition.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PSegrePartition.lean#L40-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegrePartition
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegrePartition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo (segre)
open GroundTheory.Heights₂.Heights.SegrePartition
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_SegrePartition_contDiff_segreSqSum_2a999fd991c8 :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => segreSqSum z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SegrePartition».«contDiff_segreSqSum» := P2M_GroundTheory_Heights__Heights_SegrePartition_contDiff_segreSqSum_2a999fd991c8
