-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermMinimalPolynomialDivides_eval__monic_apply_4b4fe2d5cf47
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermMinimalPolynomialDivides_eval__monic_apply_4b4fe2d5cf47
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:36.010296+00:00
-- url     : https://prove2.me/theorems/5648128b-b9d8-555c-ae13-7b0cebedeeb5
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Minimal Polynomial Divides eval  monic apply 4b4fe2d5cf47: P2 M Ground Theory Heights  Heights Indefinite Row Side
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Minimal Polynomial Divides eval  monic apply 4b4fe2d5cf47 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Minimal Polynomial Divides eval  monic apply 4b4fe2d5cf47 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermMinimalPolynomialDivides.lean#L99-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermMinimalPolynomialDivides.lean#L99-L103

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermMinimalPolynomialDivides
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreGermIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermsIntegrallyClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermMinimalPolynomialDivides
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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GermMinimalPolynomialDivides

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermMinimalPolynomialDivides_eval__monic_apply_4b4fe2d5cf47 {σ : Type} [Fintype σ] (x : σ → ℂ) {d : ℕ} (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ))
    (g : (σ → ℂ) → ℂ) {M : ℕ} (b : Fin M → analyticAtRing (A x)) (z : σ → ℂ) :
    eval₂ (preLinear x A) g (Polynomial.X ^ M + ∑ j, C (b j) * Polynomial.X ^ (j : ℕ)) z =
      g z ^ M + ∑ j, (b j).1 (A z) * g z ^ (j : ℕ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«GermMinimalPolynomialDivides».«eval₂_monic_apply» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermMinimalPolynomialDivides_eval__monic_apply_4b4fe2d5cf47
