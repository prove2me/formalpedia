-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalGraphMass_image_repr_eq_graph_e6a69d43be56
-- name    : P2M_GroundTheory_Heights__Heights_LocalGraphMass_image_repr_eq_graph_e6a69d43be56
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:49.052256+00:00
-- url     : https://prove2.me/theorems/877b01a8-c6dd-4b02-98aa-da058c55769f
-- title:
--   P2 M Ground Theory Heights  Heights Local Graph Mass image repr eq graph e6a69d43be56: P2 M Ground Theory Heights  Heights Local Graph Mass image repr eq graph e6a69d43be56
-- statement:
--   The P2 M Ground Theory Heights  Heights Local Graph Mass image repr eq graph e6a69d43be56 construction uses the P2 M Ground Theory Heights  Heights Local Graph Mass image repr eq graph e6a69d43be56 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalGraphMass.lean#L51-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalGraphMass.lean#L51-L89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalGraphMass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Function
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LocalGraphMass
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LocalGraphMass_image_repr_eq_graph_e6a69d43be56 (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I₀ : Finset (Fin n)) {d : ℕ} (hd : I₀.card = d) (Ω : Set (I₀ → ℂ))
    (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)) (hΩ : IsOpen Ω) (hg : DifferentiableOn ℂ g Ω)
    (hfix : ∀ w ∈ Ω, frameProj b I₀ (g w) = w) :
    ∃ (m : ℕ) (e : Fin n ≃ Fin d ⊕ Fin m) (Ω' : Set (EuclideanSpace ℂ (Fin d)))
      (F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m)),
      IsOpen Ω' ∧ DifferentiableOn ℂ F Ω' ∧ b.repr '' (g '' Ω) = graphPt e F '' Ω' := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LocalGraphMass».«image_repr_eq_graph» := P2M_GroundTheory_Heights__Heights_LocalGraphMass_image_repr_eq_graph_e6a69d43be56
