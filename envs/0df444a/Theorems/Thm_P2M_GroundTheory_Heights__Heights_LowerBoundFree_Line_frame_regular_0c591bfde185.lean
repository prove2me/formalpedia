-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_frame_regular_0c591bfde185
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_frame_regular_0c591bfde185
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:45:37.997039+00:00
-- url     : https://prove2.me/theorems/e08328c3-201d-43a8-9f95-9b3a1a0e72b3
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Line frame regular 0c591bfde185: P2 M Ground Theory Heights  Heights Lower Bound Free Line frame regular 0c591bfde185
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Line frame regular 0c591bfde185 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Line frame regular 0c591bfde185 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/LineMu.lean#L85-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/LineMu.lean#L85-L91

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
variable {c : Unit → Fin 2} {f : Ω} {b : Fin 2 → Fin 2 → Ω}

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_frame_regular_0c591bfde185 (hfr : IsFrameOver yLine (trivialBundle (segreCoord yLine) 2) c f b) (q p : Fin 2) :
    ∃ n : ℕ, f ^ n * b q p ∈ chartRing ℤ (segreCoord yLine) c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«Line».«frame_regular» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_frame_regular_0c591bfde185
