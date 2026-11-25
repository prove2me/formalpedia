-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_mem_lineF_apply_one_538db3f5cd9a
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_mem_lineF_apply_one_538db3f5cd9a
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:42:03.944937+00:00
-- url     : https://prove2.me/theorems/099e1c90-a00a-4384-81fa-3e9b78f4524a
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Line mem line F apply one 538db3f5cd9a: P2 M Ground Theory Heights  Heights Lower Bound Free Line mem line F apply one 538db3f5cd9a
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Line mem line F apply one 538db3f5cd9a construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Line mem line F apply one 538db3f5cd9a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/LineMu.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/LineMu.lean#L16-L18

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

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_mem_lineF_apply_one_538db3f5cd9a {v : Fin 2 → Ω} (hv : v ∈ lineF) : v 1 = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«Line».«mem_lineF_apply_one» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_mem_lineF_apply_one_538db3f5cd9a
