-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_lineHodge_aMu_944bad2d47be
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_lineHodge_aMu_944bad2d47be
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:06:19.624744+00:00
-- url     : https://prove2.me/theorems/a2ac1e7a-c301-5071-b4d9-61f7f3532744
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Line line Hodge a Mu 944bad2d47be: P2 M Ground Theory Heights  Heights Lower Bound Free Line line Hodge a Mu 944bad2d47be
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Line line Hodge a Mu 944bad2d47be construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Line line Hodge a Mu 944bad2d47be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/IsFrameOverLine.lean#L138-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/IsFrameOverLine.lean#L138-L138

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Metric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_Example
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_IsFrameOverLine
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
open GroundTheory.Heights₂.Heights.LowerBoundFree.Line

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_lineHodge_aMu_944bad2d47be (II : IntersectionSystem) (hII) : (lineHodge II hII).aMu = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«Line».«lineHodge_aMu» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_lineHodge_aMu_944bad2d47be
