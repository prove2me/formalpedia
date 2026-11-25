-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_roots_near_of_centred_22c697db77d1
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_roots_near_of_centred_22c697db77d1
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:21:43.39181+00:00
-- url     : https://prove2.me/theorems/a90a2be8-e704-4330-9f25-d34df9dac64f
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets roots near of centred 22c697db77d1: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets root
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets roots near of centred 22c697db77d1 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets roots near of centred 22c697db77d1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PevEqZeroOfPresentation.lean#L185-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PevEqZeroOfPresentation.lean#L185-L240

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitivePresentationCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PevEqZeroOfPresentation
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
open Topology Filter Polynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_roots_near_of_centred_22c697db77d1 {E : Type*} [TopologicalSpace E] {n : ℕ} (b : Fin n → E → ℂ) (y₀ : E) (u : ℂ)
    (hb : ∀ j, ContinuousAt (b j) y₀) (h0 : ∀ T : ℂ, T ^ n + ∑ j, b j y₀ * T ^ (j : ℕ) = (T - u) ^ n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 y₀, ∀ x : ℂ, x ^ n + ∑ j, b j y * x ^ (j : ℕ) = 0 → ‖x - u‖ < ε := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«roots_near_of_centred» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_roots_near_of_centred_22c697db77d1
