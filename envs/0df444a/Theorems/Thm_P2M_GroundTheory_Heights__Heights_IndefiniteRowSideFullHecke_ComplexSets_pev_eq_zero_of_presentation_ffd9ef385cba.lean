-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_eq_zero_of_presentation_ffd9ef385cba
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_eq_zero_of_presentation_ffd9ef385cba
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:35.946725+00:00
-- url     : https://prove2.me/theorems/ec804fa6-6d76-4109-91c2-1c3ce6e17338
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets pev eq zero of presentation ffd9ef385cba: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Set
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets pev eq zero of presentation ffd9ef385cba construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets pev eq zero of presentation ffd9ef385cba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PevEqZeroOfPresentation.lean#L150-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PevEqZeroOfPresentation.lean#L150-L183

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_eq_zero_of_presentation_ffd9ef385cba {σ : Type} [Fintype σ] {w : σ → ℂ} {k : ℕ} {p : Fin k → (σ → ℂ) → ℂ}
    {d : ℕ} {A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)} {ℓ : (σ → ℂ) →L[ℂ] ℂ} {N : ℕ} {c : Fin N → (Fin d → ℂ) → ℂ}
    {δ : (Fin d → ℂ) → ℂ} (hP : IsPrimitivePresentation w p A ℓ c δ) (H : (analyticSubring (A w))[X])
    (hH : IsGermCombination w p (fun z => pev (A z) (ℓ z) H)) :
    ∀ᶠ y in 𝓝 (A w), ∀ t : ℂ, t ^ N + ∑ j, c j y * t ^ (j : ℕ) = 0 → pev y t H = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«pev_eq_zero_of_presentation» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_pev_eq_zero_of_presentation_ffd9ef385cba
