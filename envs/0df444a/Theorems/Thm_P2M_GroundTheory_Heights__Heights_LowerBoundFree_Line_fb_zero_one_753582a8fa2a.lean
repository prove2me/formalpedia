-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_fb_zero_one_753582a8fa2a
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_fb_zero_one_753582a8fa2a
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:44:30.027694+00:00
-- url     : https://prove2.me/theorems/7fcb2112-2256-5a88-8ddd-f53a4958f6b5
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Line fb zero one 753582a8fa2a: P2 M Ground Theory Heights  Heights Lower Bound Free Line fb zero one 753582a8fa2a
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Line fb zero one 753582a8fa2a construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Line fb zero one 753582a8fa2a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/LineMu.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/LineMu.lean#L41-L47

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
variable {z : (Σ _ : Unit, Fin 2) → ℂ} (d : MuFrameAt (lineHodge II hII) z)

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_fb_zero_one_753582a8fa2a : fb d 0 1 = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«Line».«fb_zero_one» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_fb_zero_one_753582a8fa2a
