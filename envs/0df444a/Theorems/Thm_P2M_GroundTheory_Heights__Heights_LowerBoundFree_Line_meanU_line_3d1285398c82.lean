-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_meanU_line_3d1285398c82
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_meanU_line_3d1285398c82
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:33:42.841217+00:00
-- url     : https://prove2.me/theorems/dc032dab-99fd-5261-9320-2e12afd41fb4
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Line mean U line 3d1285398c82: P2 M Ground Theory Heights  Heights Lower Bound Free Line mean U line 3d1285398c82
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Line mean U line 3d1285398c82 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Line mean U line 3d1285398c82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/LineMu.lean#L296-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/LineMu.lean#L296-L297

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Values
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Weights
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_LineMu
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexConjugate
variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])
variable {II hII}

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_meanU_line_3d1285398c82 : meanU (lineHodge II hII) (gaussCusp II hII) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«Line».«meanU_line» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_meanU_line_3d1285398c82
