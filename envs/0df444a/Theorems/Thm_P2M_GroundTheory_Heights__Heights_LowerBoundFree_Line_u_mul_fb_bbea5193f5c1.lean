-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_u_mul_fb_bbea5193f5c1
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_u_mul_fb_bbea5193f5c1
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:45:53.234737+00:00
-- url     : https://prove2.me/theorems/558d7da2-9686-5a68-afcd-327e98367f2b
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Line u mul fb bbea5193f5c1: P2 M Ground Theory Heights  Heights Lower Bound Free Line u mul fb bbea5193f5c1
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Line u mul fb bbea5193f5c1 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Line u mul fb bbea5193f5c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/LineMu.lean#L50-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/LineMu.lean#L50-L72

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
set_option maxHeartbeats 2000000

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_u_mul_fb_bbea5193f5c1 : d.u * fb d 1 1 = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«Line».«u_mul_fb» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_u_mul_fb_bbea5193f5c1
