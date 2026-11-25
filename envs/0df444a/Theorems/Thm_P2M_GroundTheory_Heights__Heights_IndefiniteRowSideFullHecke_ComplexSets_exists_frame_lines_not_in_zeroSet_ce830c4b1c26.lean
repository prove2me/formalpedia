-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_frame_lines_not_in_zeroSet_ce830c4b1c26
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_frame_lines_not_in_zeroSet_ce830c4b1c26
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:20:40.723185+00:00
-- url     : https://prove2.me/theorems/d57741fa-10e3-5373-8325-8544f0f70dd0
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists frame lines not in zero Set ce830c4b1c26: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Comp
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists frame lines not in zero Set ce830c4b1c26 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists frame lines not in zero Set ce830c4b1c26 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PolynomialFrame.lean#L78-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PolynomialFrame.lean#L78-L101

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PolynomialFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Filter Topology
noncomputable section
open PolynomialFrame

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_frame_lines_not_in_zeroSet_ce830c4b1c26 {k : ℕ} {P : MvPolynomial (Fin k) ℂ} (hP : P ≠ 0) :
    ∃ M : Matrix (Fin k) (Fin k) ℂ, M.det ≠ 0 ∧
      ∀ (i : Fin k) (w : Fin k → ℂ), ∃ t : ℂ, eval (w + t • fun j => M j i) P ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«exists_frame_lines_not_in_zeroSet» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_frame_lines_not_in_zeroSet_ce830c4b1c26
