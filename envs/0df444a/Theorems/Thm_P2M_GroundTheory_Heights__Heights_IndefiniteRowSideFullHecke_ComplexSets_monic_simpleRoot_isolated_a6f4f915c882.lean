-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_simpleRoot_isolated_a6f4f915c882
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_simpleRoot_isolated_a6f4f915c882
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:23:02.25475+00:00
-- url     : https://prove2.me/theorems/fe4e6cd2-ef08-4ca1-8ac0-5fe4fc4a8195
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets monic simple Root isolated a6f4f915c882: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets monic simple Root isolated a6f4f915c882 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets monic simple Root isolated a6f4f915c882 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitiveFormSheetedIffRootFull.lean#L9-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitiveFormSheetedIffRootFull.lean#L9-L45

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitiveFormSheetedIffRootFull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitiveFormSheetedIffRootFull
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_simpleRoot_isolated_a6f4f915c882 {d N : ℕ} (a : Fin N → (Fin d → ℂ) → ℂ) (t : Fin d → ℂ) (τ : ℂ)
    (hcont : ∀ j, ContinuousAt (a j) t)
    (hsep : (Polynomial.X ^ N + ∑ j, Polynomial.C (a j t) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable)
    (hroot : τ ^ N + ∑ j, a j t * τ ^ (j : ℕ) = 0) :
    ∃ ε > 0, ∀ s, dist s t < ε → ∀ T₁ T₂ : ℂ, dist T₁ τ < ε → dist T₂ τ < ε →
      T₁ ^ N + ∑ j, a j s * T₁ ^ (j : ℕ) = 0 → T₂ ^ N + ∑ j, a j s * T₂ ^ (j : ℕ) = 0 → T₁ = T₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«monic_simpleRoot_isolated» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_monic_simpleRoot_isolated_a6f4f915c882
