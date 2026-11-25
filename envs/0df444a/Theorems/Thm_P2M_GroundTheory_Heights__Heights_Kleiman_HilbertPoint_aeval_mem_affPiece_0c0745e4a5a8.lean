-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_aeval_mem_affPiece_0c0745e4a5a8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_aeval_mem_affPiece_0c0745e4a5a8
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:55:49.071284+00:00
-- url     : https://prove2.me/theorems/414a7c57-3f7c-4c4e-aac3-846038aabddd
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Hilbert Point aeval mem aff Piece 0c0745e4a5a8: P2 M Ground Theory Heights  Heights Kleiman Hilbert Point aeval mem aff Piece 0c0745e4a5a8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Hilbert Point aeval mem aff Piece 0c0745e4a5a8 construction uses the P2 M Ground Theory Heights  Heights Kleiman Hilbert Point aeval mem aff Piece 0c0745e4a5a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PHilbertPoint.lean#L134-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PHilbertPoint.lean#L134-L140

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
variable {y : Fin (N + 1) → Ω} {j : Fin (N + 1)}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_aeval_mem_affPiece_0c0745e4a5a8 (hj : y j ≠ 0) (f : Poly k N) :
    aeval (aff y j) f ∈ affPiece k y j f.totalDegree := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«HilbertPoint».«aeval_mem_affPiece» := P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_aeval_mem_affPiece_0c0745e4a5a8
