-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_affPiece_le_b8daa26183c8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_affPiece_le_b8daa26183c8
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:55:49.545818+00:00
-- url     : https://prove2.me/theorems/bcdc98e8-ea76-4b72-b9b0-55b22f5ecc8a
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Hilbert Point aff Piece le b8daa26183c8: P2 M Ground Theory Heights  Heights Kleiman Hilbert Point aff Piece le b8daa26183c8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Hilbert Point aff Piece le b8daa26183c8 construction uses the P2 M Ground Theory Heights  Heights Kleiman Hilbert Point aff Piece le b8daa26183c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PHilbertPoint.lean#L122-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PHilbertPoint.lean#L122-L123

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_affPiece_le_b8daa26183c8 (n : ℕ) : affPiece k y j n ≤ Subalgebra.toSubmodule (affRing k y j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«HilbertPoint».«affPiece_le» := P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_affPiece_le_b8daa26183c8
