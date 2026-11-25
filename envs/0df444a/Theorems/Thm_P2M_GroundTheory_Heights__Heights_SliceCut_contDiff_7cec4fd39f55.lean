-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_contDiff_7cec4fd39f55
-- name    : P2M_GroundTheory_Heights__Heights_SliceCut_contDiff_7cec4fd39f55
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:04.314285+00:00
-- url     : https://prove2.me/theorems/2bc03c65-2bc3-40e4-8a6f-b155f885656e
-- title:
--   P2 M Ground Theory Heights  Heights Slice Cut cont Diff 7cec4fd39f55: P2 M Ground Theory Heights  Heights Slice Cut cont Diff 7cec4fd39f55
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Cut cont Diff 7cec4fd39f55 construction uses the P2 M Ground Theory Heights  Heights Slice Cut cont Diff 7cec4fd39f55 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/SliceCut.lean#L53-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/SliceCut.lean#L53-L63

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

theorem P2M_GroundTheory_Heights__Heights_SliceCut_contDiff_7cec4fd39f55 (k : ℕ) : ContDiff ℝ ∞ (sliceCut h k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceCut».«contDiff» := P2M_GroundTheory_Heights__Heights_SliceCut_contDiff_7cec4fd39f55
