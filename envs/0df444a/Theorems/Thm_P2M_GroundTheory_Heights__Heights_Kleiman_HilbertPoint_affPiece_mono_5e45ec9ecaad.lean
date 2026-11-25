-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_affPiece_mono_5e45ec9ecaad
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_affPiece_mono_5e45ec9ecaad
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:21:55.790499+00:00
-- url     : https://prove2.me/theorems/23495eac-f0cf-52de-a5c3-e88cf8ecce37
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Hilbert Point aff Piece mono 5e45ec9ecaad: P2 M Ground Theory Heights  Heights Kleiman Hilbert Point aff Piece mono 5e45ec9ecaad
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Hilbert Point aff Piece mono 5e45ec9ecaad construction uses the P2 M Ground Theory Heights  Heights Kleiman Hilbert Point aff Piece mono 5e45ec9ecaad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PHilbertPoint.lean#L125-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PHilbertPoint.lean#L125-L132

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_affPiece_mono_5e45ec9ecaad (hj : y j ≠ 0) {m n : ℕ} (h : m ≤ n) :
    affPiece k y j m ≤ affPiece k y j n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«HilbertPoint».«affPiece_mono» := P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_affPiece_mono_5e45ec9ecaad
