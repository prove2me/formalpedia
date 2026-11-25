-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_quotNormSq_line_f2898b3301f1
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_quotNormSq_line_f2898b3301f1
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:45:50.785554+00:00
-- url     : https://prove2.me/theorems/6e7025d6-5b4c-4183-97ff-f8e95d52be37
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Line quot Norm Sq line f2898b3301f1: P2 M Ground Theory Heights  Heights Lower Bound Free Line quot Norm Sq line f2898b3301f1
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Line quot Norm Sq line f2898b3301f1 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Line quot Norm Sq line f2898b3301f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/LineMu.lean#L133-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/LineMu.lean#L133-L152

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
variable {z : (Σ _ : Unit, Fin 2) → ℂ}

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_quotNormSq_line_f2898b3301f1 (S : Matrix (Fin 2) (Fin 2) ℂ) (h10 : S 1 0 = 0) (h00 : S 0 0 ≠ 0) :
    quotNormSq (show 1 ≤ 2 by decide) (Sᴴ * S) = ‖S 1 1‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«Line».«quotNormSq_line» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_quotNormSq_line_f2898b3301f1
