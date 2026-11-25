-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_coordGraded_piece_le_secs_7b0b7b96dc1e
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_coordGraded_piece_le_secs_7b0b7b96dc1e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:29:16.433889+00:00
-- url     : https://prove2.me/theorems/60c3123b-86de-42c2-927b-9cf1ff65ee57
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman coord Graded piece le secs 7b0b7b96dc1e: P2 M Ground Theory Heights  Heights Kleiman coord Graded piece le secs 7b0b7b96dc1e
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman coord Graded piece le secs 7b0b7b96dc1e construction uses the P2 M Ground Theory Heights  Heights Kleiman coord Graded piece le secs 7b0b7b96dc1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistSections.lean#L54-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistSections.lean#L54-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsTwistSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotGraded
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistSections
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
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  (y : Fin (N + 1) → Ω)

theorem P2M_GroundTheory_Heights__Heights_Kleiman_coordGraded_piece_le_secs_7b0b7b96dc1e (n : ℕ) :
    (coordGraded S y).piece (n : ℤ) ≤ (twistSys S y (n : ℤ)).secs := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«coordGraded_piece_le_secs» := P2M_GroundTheory_Heights__Heights_Kleiman_coordGraded_piece_le_secs_7b0b7b96dc1e
