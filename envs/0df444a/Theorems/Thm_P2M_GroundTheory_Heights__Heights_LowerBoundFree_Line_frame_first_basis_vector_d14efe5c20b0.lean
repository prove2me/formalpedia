-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_frame_first_basis_vector_d14efe5c20b0
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_frame_first_basis_vector_d14efe5c20b0
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:44:36.922941+00:00
-- url     : https://prove2.me/theorems/d200b948-0bd0-5c7d-9881-490bb965ef24
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Line frame first basis vector d14efe5c20b0: P2 M Ground Theory Heights  Heights Lower Bound Free Line frame first basis vector d14efe5c20b0
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Line frame first basis vector d14efe5c20b0 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Line frame first basis vector d14efe5c20b0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/LineMu.lean#L93-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/LineMu.lean#L93-L101

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

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_frame_first_basis_vector_d14efe5c20b0 (hfr : IsFrameOver yLine (trivialBundle (segreCoord yLine) 2) c f b) :
    ∃ a : Fin 2 → Ω, (∀ q, ∃ n : ℕ, f ^ n * a q ∈ chartRing ℤ (segreCoord yLine) c) ∧
      (Pi.single 0 1 : Fin 2 → Ω) = ∑ q, a q • b q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«Line».«frame_first_basis_vector» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_frame_first_basis_vector_d14efe5c20b0
