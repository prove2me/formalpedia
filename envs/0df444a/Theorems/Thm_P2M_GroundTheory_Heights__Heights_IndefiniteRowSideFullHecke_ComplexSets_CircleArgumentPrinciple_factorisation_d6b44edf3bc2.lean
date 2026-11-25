-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CircleArgumentPrinciple_factorisation_d6b44edf3bc2
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CircleArgumentPrinciple_factorisation_d6b44edf3bc2
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:56.157806+00:00
-- url     : https://prove2.me/theorems/e0a4055a-63aa-4e01-b768-f3cc0169d8a2
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Circle Argument Principle factorisation d6b44edf3bc2: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Circle Argument Principle factorisation d6b44edf3bc2 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Circle Argument Principle factorisation d6b44edf3bc2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCircleArgumentPrinciple.lean#L93-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCircleArgumentPrinciple.lean#L93-L229

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCircleArgumentPrinciple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCircleArgumentPrinciple
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
open Topology Filter Metric Complex Real
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CircleArgumentPrinciple_factorisation_d6b44edf3bc2 {h : ℂ → ℂ} {O : Set ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hO : IsOpen O) (hball : closedBall c r ⊆ O) (hh : DifferentiableOn ℂ h O)
    (hsph : ∀ s ∈ sphere c r, h s ≠ 0) :
    ∃ (Z : Multiset ℂ) (u : ℂ → ℂ),
      (∀ a ∈ Z, a ∈ ball c r) ∧ DifferentiableOn ℂ u O ∧ (∀ s ∈ closedBall c r, u s ≠ 0) ∧
      (∀ s ∈ O, h s = (Z.map fun a => s - a).prod * u s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«CircleArgumentPrinciple».«factorisation» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CircleArgumentPrinciple_factorisation_d6b44edf3bc2
