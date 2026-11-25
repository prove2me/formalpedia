-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_OsgoodSeparate_cons_mem_ball_309c0470889e
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_OsgoodSeparate_cons_mem_ball_309c0470889e
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:19:51.995801+00:00
-- url     : https://prove2.me/theorems/579c7a11-93f4-461f-9426-fdd819ba7a41
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Osgood Separate cons mem ball 309c0470889e: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex S
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Osgood Separate cons mem ball 309c0470889e construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Osgood Separate cons mem ball 309c0470889e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/OsgoodSeparate.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/OsgoodSeparate.lean#L16-L22

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_OsgoodSeparate_cons_mem_ball_309c0470889e {n : ℕ} {c : Fin (n + 1) → ℂ} {R : ℝ} {x : ℂ} (hx : x ∈ ball (c 0) R)
    {y : Fin n → ℂ} (hy : y ∈ ball (Fin.tail c) R) : (Fin.cons x y : Fin (n + 1) → ℂ) ∈ ball c R := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«OsgoodSeparate».«cons_mem_ball» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_OsgoodSeparate_cons_mem_ball_309c0470889e
