-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CircleArgumentPrinciple_integral_prod_mul_c8dc6c3455c8
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CircleArgumentPrinciple_integral_prod_mul_c8dc6c3455c8
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:40.169094+00:00
-- url     : https://prove2.me/theorems/44c23ede-703e-53e4-9fbd-07b6a79156ad
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Circle Argument Principle integral prod mul c8dc6c3455c8: P2 M Ground Theory Heights  Heights Indefinite Row Side Full H
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Circle Argument Principle integral prod mul c8dc6c3455c8 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Circle Argument Principle integral prod mul c8dc6c3455c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCircleArgumentPrinciple.lean#L19-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PCircleArgumentPrinciple.lean#L19-L91

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CircleArgumentPrinciple_integral_prod_mul_c8dc6c3455c8 {O : Set ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r) (hO : IsOpen O)
    (hball : closedBall c r ⊆ O) {u φ : ℂ → ℂ} (hu : DifferentiableOn ℂ u O)
    (hu0 : ∀ s ∈ closedBall c r, u s ≠ 0) (hφ : DifferentiableOn ℂ φ O) (Z : Multiset ℂ)
    (hZ : ∀ a ∈ Z, a ∈ ball c r) :
    (2 * π * I)⁻¹ * (∮ s in C(c, r), φ s * deriv (fun s => (Z.map fun a => s - a).prod * u s) s /
      ((Z.map fun a => s - a).prod * u s)) = (Z.map φ).sum := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«CircleArgumentPrinciple».«integral_prod_mul» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_CircleArgumentPrinciple_integral_prod_mul_c8dc6c3455c8
