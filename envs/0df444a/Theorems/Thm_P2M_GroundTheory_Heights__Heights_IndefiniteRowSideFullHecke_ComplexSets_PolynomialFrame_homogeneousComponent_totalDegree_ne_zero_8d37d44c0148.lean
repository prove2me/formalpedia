-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialFrame_homogeneousComponent_totalDegree_ne_zero_8d37d44c0148
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialFrame_homogeneousComponent_totalDegree_ne_zero_8d37d44c0148
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:20:00.639712+00:00
-- url     : https://prove2.me/theorems/b30bc36f-df7f-4b81-8827-47ba04761fb1
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Polynomial Frame homogeneous Component total Degree ne zero 8d37d44c0148: P2 M Ground Theory Heights  Heights Indefinite
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Polynomial Frame homogeneous Component total Degree ne zero 8d37d44c0148 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Polynomial Frame homogeneous Component total Degree ne zero 8d37d44c0148 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PolynomialFrame.lean#L63-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PolynomialFrame.lean#L63-L72

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialFrame_homogeneousComponent_totalDegree_ne_zero_8d37d44c0148 {k : ℕ} {P : MvPolynomial (Fin k) ℂ} (hP : P ≠ 0) :
    homogeneousComponent P.totalDegree P ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«PolynomialFrame».«homogeneousComponent_totalDegree_ne_zero» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialFrame_homogeneousComponent_totalDegree_ne_zero_8d37d44c0148
