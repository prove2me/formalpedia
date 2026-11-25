-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_hasCompactSupport_bc9ece2fd11b
-- name    : P2M_GroundTheory_Heights__Heights_SliceCut_hasCompactSupport_bc9ece2fd11b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:37:46.631803+00:00
-- url     : https://prove2.me/theorems/80697390-27a3-4f48-bfc7-16c7b1db06b9
-- title:
--   P2 M Ground Theory Heights  Heights Slice Cut has Compact Support bc9ece2fd11b: P2 M Ground Theory Heights  Heights Slice Cut has Compact Support bc9ece2fd11b
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Cut has Compact Support bc9ece2fd11b construction uses the P2 M Ground Theory Heights  Heights Slice Cut has Compact Support bc9ece2fd11b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/SliceCut.lean#L65-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/SliceCut.lean#L65-L75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology Matrix
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.SliceCut
variable {n : ℕ} (h : HermNorm n)

theorem P2M_GroundTheory_Heights__Heights_SliceCut_hasCompactSupport_bc9ece2fd11b (k : ℕ) : HasCompactSupport (sliceCut h k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceCut».«hasCompactSupport» := P2M_GroundTheory_Heights__Heights_SliceCut_hasCompactSupport_bc9ece2fd11b
