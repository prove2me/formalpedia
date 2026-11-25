-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermMinimalPolynomialDivides_eventually_of_germ_eq_29ea61993c1c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermMinimalPolynomialDivides_eventually_of_germ_eq_29ea61993c1c
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:22:11.8302+00:00
-- url     : https://prove2.me/theorems/04742387-c83e-5fc1-a54e-cc6fecd01ee3
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Minimal Polynomial Divides eventually of germ eq 29ea61993c1c: P2 M Ground Theory Heights  Heights Indefinite Row S
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Minimal Polynomial Divides eventually of germ eq 29ea61993c1c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Minimal Polynomial Divides eventually of germ eq 29ea61993c1c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermMinimalPolynomialDivides.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermMinimalPolynomialDivides.lean#L87-L89

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermMinimalPolynomialDivides_eventually_of_germ_eq_29ea61993c1c {σ : Type} [Fintype σ] {X : Set (σ → ℂ)} {x : σ → ℂ} {f g : (σ → ℂ) → ℂ}
    (h : (f : Germ (𝓝[X] x) ℂ) = g) : ∀ᶠ z in 𝓝 x, z ∈ X → f z = g z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«GermMinimalPolynomialDivides».«eventually_of_germ_eq» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermMinimalPolynomialDivides_eventually_of_germ_eq_29ea61993c1c
