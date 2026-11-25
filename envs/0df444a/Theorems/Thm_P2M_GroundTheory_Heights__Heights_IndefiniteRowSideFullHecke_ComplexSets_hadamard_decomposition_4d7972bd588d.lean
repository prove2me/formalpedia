-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hadamard_decomposition_4d7972bd588d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hadamard_decomposition_4d7972bd588d
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:21:08.076875+00:00
-- url     : https://prove2.me/theorems/250a64e1-8380-4976-ad6f-4e5977445814
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets hadamard decomposition 4d7972bd588d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets had
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets hadamard decomposition 4d7972bd588d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets hadamard decomposition 4d7972bd588d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHolGermPointIdealSpan.lean#L10-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHolGermPointIdealSpan.lean#L10-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermPointIdealSpan
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolGermPointIdealSpan
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
open MvPolynomial Topology Filter

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hadamard_decomposition_4d7972bd588d {σ : Type} [Fintype σ] {w : σ → ℂ} {f : (σ → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f w) :
    ∃ g : σ → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (g i) w) ∧
      ∀ᶠ z in 𝓝 w, f z = f w + ∑ i, (z i - w i) * g i z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«hadamard_decomposition» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hadamard_decomposition_4d7972bd588d
