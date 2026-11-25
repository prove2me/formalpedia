-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_X_single_975289589ee1
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_X_single_975289589ee1
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:14:31.396399+00:00
-- url     : https://prove2.me/theorems/dbed4f27-9700-401c-b43b-59c2028c6d97
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog X single 975289589ee1: P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog X single 975289589ee1
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog X single 975289589ee1 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free is Multi Homog X single 975289589ee1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Values.lean#L52-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Values.lean#L52-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_IsFrameOverLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Values
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
open scoped Matrix
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_X_single_975289589ee1 [DecidableEq K] (p : Σ k, ι k) :
    IsMultiHomog (X p : MRing ι) (fun k => if k = p.1 then 1 else 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«isMultiHomog_X_single» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_isMultiHomog_X_single_975289589ee1
