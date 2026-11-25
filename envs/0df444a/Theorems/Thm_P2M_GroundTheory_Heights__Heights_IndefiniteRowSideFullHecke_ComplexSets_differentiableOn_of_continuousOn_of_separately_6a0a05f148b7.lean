-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_differentiableOn_of_continuousOn_of_separately_6a0a05f148b7
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_differentiableOn_of_continuousOn_of_separately_6a0a05f148b7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:20:41.28628+00:00
-- url     : https://prove2.me/theorems/cd5afc85-b3ee-4e32-9dff-2c9508333528
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets differentiable On of continuous On of separately 6a0a05f148b7: P2 M Ground Theory Heights  Heights Indefinite Row Side F
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets differentiable On of continuous On of separately 6a0a05f148b7 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets differentiable On of continuous On of separately 6a0a05f148b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/OsgoodSeparate.lean#L113-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/OsgoodSeparate.lean#L113-L117

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_differentiableOn_of_continuousOn_of_separately_6a0a05f148b7 {n : ℕ} {U : Set (Fin n → ℂ)}
    {g : (Fin n → ℂ) → ℂ} (hU : IsOpen U) (hc : ContinuousOn g U)
    (hs : ∀ z ∈ U, ∀ i, DifferentiableAt ℂ (fun t => g (Function.update z i t)) (z i)) :
    DifferentiableOn ℂ g U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«differentiableOn_of_continuousOn_of_separately» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_differentiableOn_of_continuousOn_of_separately_6a0a05f148b7
