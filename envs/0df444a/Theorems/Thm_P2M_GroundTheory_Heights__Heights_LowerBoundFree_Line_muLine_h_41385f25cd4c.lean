-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_muLine_h_41385f25cd4c
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_muLine_h_41385f25cd4c
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:43:14.109487+00:00
-- url     : https://prove2.me/theorems/f91acee4-e8b2-5228-bc5d-1dca94429981
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Line mu Line h 41385f25cd4c: P2 M Ground Theory Heights  Heights Lower Bound Free Line mu Line h 41385f25cd4c
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Line mu Line h 41385f25cd4c construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Line mu Line h 41385f25cd4c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/LineMu.lean#L244-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/LineMu.lean#L244-L260

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

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_muLine_h_41385f25cd4c {z : (Σ _ : Unit, Fin 2) → ℂ} (hz : ∃ i, z ⟨(), i⟩ ≠ 0) :
    (muLine (lineHodge II hII)).h z = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«Line».«muLine_h» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_muLine_h_41385f25cd4c
