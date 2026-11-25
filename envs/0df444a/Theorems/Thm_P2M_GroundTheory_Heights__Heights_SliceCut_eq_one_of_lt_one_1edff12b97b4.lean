-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_eq_one_of_lt_one_1edff12b97b4
-- name    : P2M_GroundTheory_Heights__Heights_SliceCut_eq_one_of_lt_one_1edff12b97b4
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:37:40.18502+00:00
-- url     : https://prove2.me/theorems/893d893d-de48-4d5c-b61a-35b9624537dc
-- title:
--   P2 M Ground Theory Heights  Heights Slice Cut eq one of lt one 1edff12b97b4: P2 M Ground Theory Heights  Heights Slice Cut eq one of lt one 1edff12b97b4
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Cut eq one of lt one 1edff12b97b4 construction uses the P2 M Ground Theory Heights  Heights Slice Cut eq one of lt one 1edff12b97b4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/SliceCut.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/SliceCut.lean#L46-L51

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

theorem P2M_GroundTheory_Heights__Heights_SliceCut_eq_one_of_lt_one_1edff12b97b4 (k : ℕ) {x : Fin n → ℂ} (hx : h.dualNorm x < 1) : sliceCut h k x = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceCut».«eq_one_of_lt_one» := P2M_GroundTheory_Heights__Heights_SliceCut_eq_one_of_lt_one_1edff12b97b4
