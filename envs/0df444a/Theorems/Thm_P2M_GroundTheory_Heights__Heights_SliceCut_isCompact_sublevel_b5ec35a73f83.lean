-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_isCompact_sublevel_b5ec35a73f83
-- name    : P2M_GroundTheory_Heights__Heights_SliceCut_isCompact_sublevel_b5ec35a73f83
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:38:24.248893+00:00
-- url     : https://prove2.me/theorems/2c1b7e03-df22-4cda-9215-421f1982cd76
-- title:
--   P2 M Ground Theory Heights  Heights Slice Cut is Compact sublevel b5ec35a73f83: P2 M Ground Theory Heights  Heights Slice Cut is Compact sublevel b5ec35a73f83
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Cut is Compact sublevel b5ec35a73f83 construction uses the P2 M Ground Theory Heights  Heights Slice Cut is Compact sublevel b5ec35a73f83 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/SliceCut.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/SliceCut.lean#L34-L41

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

theorem P2M_GroundTheory_Heights__Heights_SliceCut_isCompact_sublevel_b5ec35a73f83 (R : ℝ) : IsCompact {x : Fin n → ℂ | h.dualNorm x ≤ R} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceCut».«isCompact_sublevel» := P2M_GroundTheory_Heights__Heights_SliceCut_isCompact_sublevel_b5ec35a73f83
