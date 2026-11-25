-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_eq_zero_or_isHomogeneous_of_mem_piece_5f1230198ef9
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_eq_zero_or_isHomogeneous_of_mem_piece_5f1230198ef9
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:27:41.85327+00:00
-- url     : https://prove2.me/theorems/24f6782c-0232-4600-a481-7da2ab030a0e
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman eq zero or is Homogeneous of mem piece 5f1230198ef9: P2 M Ground Theory Heights  Heights Kleiman eq zero or is Homogeneous of mem piece 5f1230198ef9
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman eq zero or is Homogeneous of mem piece 5f1230198ef9 construction uses the P2 M Ground Theory Heights  Heights Kleiman eq zero or is Homogeneous of mem piece 5f1230198ef9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreOnto.lean#L29-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSerreOnto.lean#L29-L47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerreOnto
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
open MvPolynomial
noncomputable section
universe u v w w'
variable {S : Type u} [CommRing S] {N : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_eq_zero_or_isHomogeneous_of_mem_piece_5f1230198ef9 {p : Poly S N} {e : ℤ}
    (hp : p ∈ (polyGraded S N).piece e) : p = 0 ∨ ∃ n : ℕ, (n : ℤ) = e ∧ p.IsHomogeneous n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«eq_zero_or_isHomogeneous_of_mem_piece» := P2M_GroundTheory_Heights__Heights_Kleiman_eq_zero_or_isHomogeneous_of_mem_piece_5f1230198ef9
