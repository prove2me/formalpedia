-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_OsgoodSeparate_cauchy_torus_ff70d79abd01
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_OsgoodSeparate_cauchy_torus_ff70d79abd01
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:20:30.84084+00:00
-- url     : https://prove2.me/theorems/ed5c9aad-90a0-57a4-a731-de4cdce2ff56
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Osgood Separate cauchy torus ff70d79abd01: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Se
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Osgood Separate cauchy torus ff70d79abd01 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Osgood Separate cauchy torus ff70d79abd01 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/OsgoodSeparate.lean#L24-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/OsgoodSeparate.lean#L24-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PRiemannExtensionSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
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
open Complex Metric MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.Osgood
  GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.OsgoodSeparate

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_OsgoodSeparate_cauchy_torus_ff70d79abd01 : ∀ (n : ℕ) (G : (Fin n → ℂ) → ℂ) (c : Fin n → ℂ) (R : ℝ),
    ContinuousOn G (ball c R) →
    (∀ z ∈ ball c R, ∀ i, DifferentiableAt ℂ (fun t => G (Function.update z i t)) (z i)) →
    ∀ r : ℝ, 0 < r → r < R → ∀ z ∈ ball c r,
    (∯ ζ in T(c, fun _ => r), (∏ i, (ζ i - z i)⁻¹) * G ζ) = (2 * π * I) ^ n * G z
  := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«OsgoodSeparate».«cauchy_torus» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_OsgoodSeparate_cauchy_torus_ff70d79abd01
