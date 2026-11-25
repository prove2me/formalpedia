-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_sub_d1cc7c10540b
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_sub_d1cc7c10540b
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:28:19.61958+00:00
-- url     : https://prove2.me/theorems/d586dd38-0b14-4a98-a403-62797c85be57
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog sub d1cc7c10540b: P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog sub d1cc7c10540b
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog sub d1cc7c10540b construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog sub d1cc7c10540b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Metric.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Metric.lean#L18-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Metric
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω]
omit [Fintype K]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_sub_d1cc7c10540b {g h : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    (hh : IsMultiHomog h d) : IsMultiHomog (g - h) d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«isMultiHomog_sub» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_sub_d1cc7c10540b
