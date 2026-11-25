-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_norm_coord_le_bd62cc5d91a9
-- name    : P2M_GroundTheory_Heights__Heights_SliceCut_norm_coord_le_bd62cc5d91a9
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:23.360121+00:00
-- url     : https://prove2.me/theorems/7d7cc72b-c2e3-4062-91c0-42ec7841e227
-- title:
--   P2 M Ground Theory Heights  Heights Slice Cut norm coord le bd62cc5d91a9: P2 M Ground Theory Heights  Heights Slice Cut norm coord le bd62cc5d91a9
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Cut norm coord le bd62cc5d91a9 construction uses the P2 M Ground Theory Heights  Heights Slice Cut norm coord le bd62cc5d91a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/SliceCut.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/SliceCut.lean#L24-L28

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

theorem P2M_GroundTheory_Heights__Heights_SliceCut_norm_coord_le_bd62cc5d91a9 (x : Fin n → ℂ) (i : Fin n) : ‖((h.matᵀ)⁻¹ *ᵥ x) i‖ ≤ h.dualNorm x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceCut».«norm_coord_le» := P2M_GroundTheory_Heights__Heights_SliceCut_norm_coord_le_bd62cc5d91a9
