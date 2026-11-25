-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_local_filter_eq_81399f299053
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_local_filter_eq_81399f299053
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:20:17.368312+00:00
-- url     : https://prove2.me/theorems/f23a0c4c-1022-42c2-8522-f4e96ab50a82
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Polynomial Root Predicate Factor local filter eq 81399f299053: P2 M Ground Theory Heights  Heights Indefinite Row Side F
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Polynomial Root Predicate Factor local filter eq 81399f299053 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Polynomial Root Predicate Factor local filter eq 81399f299053 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPolynomialRootPredicateFactor.lean#L122-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPolynomialRootPredicateFactor.lean#L122-L195

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolynomialRootPredicateFactor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticRootBranch
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PManifoldZerosComplementConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPolynomialRootPredicateFactor
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
open Polynomial Filter Topology Classical
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.PolynomialRootPredicateFactor

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_local_filter_eq_81399f299053 {d N : ℕ} {a : Fin N → (Fin d → ℂ) → ℂ} {Q : (Fin d → ℂ) → ℂ → Prop}
    {t₀ : Fin d → ℂ} (ha : ∀ j, AnalyticAt ℂ (a j) t₀) (hsep : (fiberPoly a t₀).Separable)
    (hbr : ∀ τ₀ : ℂ, τ₀ ^ N + ∑ j, a j t₀ * τ₀ ^ (j : ℕ) = 0 →
      ∃ (O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ), IsOpen O ∧ t₀ ∈ O ∧ ContinuousOn r O ∧ r t₀ = τ₀ ∧
        ∀ s ∈ O, r s ^ N + ∑ j, a j s * r s ^ (j : ℕ) = 0 ∧ (Q s (r s) ↔ Q t₀ τ₀)) :
    ∃ ρ : ℂ → (Fin d → ℂ) → ℂ, (∀ τ, DifferentiableAt ℂ (ρ τ) t₀) ∧
      ∀ᶠ s in 𝓝 t₀, (fiberPoly a s).roots.filter (Q s) =
        ((fiberPoly a t₀).roots.filter (Q t₀)).map fun τ => ρ τ s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«PolynomialRootPredicateFactor».«local_filter_eq» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_local_filter_eq_81399f299053
