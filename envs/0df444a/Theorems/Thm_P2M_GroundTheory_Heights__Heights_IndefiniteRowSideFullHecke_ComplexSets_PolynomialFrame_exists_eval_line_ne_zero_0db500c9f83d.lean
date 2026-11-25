-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialFrame_exists_eval_line_ne_zero_0db500c9f83d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialFrame_exists_eval_line_ne_zero_0db500c9f83d
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:20:10.575176+00:00
-- url     : https://prove2.me/theorems/ee521ef4-3d30-539c-a94a-ee9d697b8a6a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Polynomial Frame exists eval line ne zero 0db500c9f83d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hec
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Polynomial Frame exists eval line ne zero 0db500c9f83d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Polynomial Frame exists eval line ne zero 0db500c9f83d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PolynomialFrame.lean#L27-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PolynomialFrame.lean#L27-L61

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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialFrame

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialFrame_exists_eval_line_ne_zero_0db500c9f83d {k : ℕ} (P : MvPolynomial (Fin k) ℂ) (v : Fin k → ℂ)
    (hv : eval v (homogeneousComponent P.totalDegree P) ≠ 0) (w : Fin k → ℂ) :
    ∃ t : ℂ, eval (w + t • v) P ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«PolynomialFrame».«exists_eval_line_ne_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialFrame_exists_eval_line_ne_zero_0db500c9f83d
