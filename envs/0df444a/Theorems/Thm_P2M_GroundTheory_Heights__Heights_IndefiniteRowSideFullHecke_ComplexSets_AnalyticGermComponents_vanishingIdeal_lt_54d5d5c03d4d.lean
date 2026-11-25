-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_vanishingIdeal_lt_54d5d5c03d4d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_vanishingIdeal_lt_54d5d5c03d4d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:20:04.493918+00:00
-- url     : https://prove2.me/theorems/870fb1cd-72b3-4b24-9521-6e55aef0b2f5
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Analytic Germ Components vanishing Ideal lt 54d5d5c03d4d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full H
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Analytic Germ Components vanishing Ideal lt 54d5d5c03d4d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Analytic Germ Components vanishing Ideal lt 54d5d5c03d4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAnalyticGermComponents.lean#L81-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAnalyticGermComponents.lean#L81-L88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermComponents
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
open Topology Filter
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AnalyticGermComponents
variable {σ : Type} [Fintype σ]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_vanishingIdeal_lt_54d5d5c03d4d {X : Set (σ → ℂ)} {w : σ → ℂ} {f : (σ → ℂ) → ℂ} (hf : AnalyticAt ℂ f w)
    (hnf : ¬ ∀ᶠ z in 𝓝 w, z ∈ X → f z = 0) :
    vanishingIdeal X w < vanishingIdeal (X ∩ {z | f z = 0}) w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«AnalyticGermComponents».«vanishingIdeal_lt» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AnalyticGermComponents_vanishingIdeal_lt_54d5d5c03d4d
