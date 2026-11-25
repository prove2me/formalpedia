-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermMinimalPolynomialDivides_coe_eval__map_ee79be857def
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermMinimalPolynomialDivides_coe_eval__map_ee79be857def
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:21:45.437124+00:00
-- url     : https://prove2.me/theorems/b83c5c23-1162-4c4d-8fb0-3b10f2c1e5eb
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Minimal Polynomial Divides coe eval  map ee79be857def: P2 M Ground Theory Heights  Heights Indefinite Row Side Full
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Minimal Polynomial Divides coe eval  map ee79be857def construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Germ Minimal Polynomial Divides coe eval  map ee79be857def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermMinimalPolynomialDivides.lean#L91-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermMinimalPolynomialDivides.lean#L91-L97

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermMinimalPolynomialDivides_coe_eval__map_ee79be857def {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (x : σ → ℂ) {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (P : (analyticAtRing (A x))[X]) (v : analyticAtRing x) :
    ((eval₂ (alongPull X x A) (alongOf X x v) (P.map (germOf (A x))) : germsAlong X x) : Germ (𝓝[X] x) ℂ) =
      ((eval₂ (preLinear x A) v.1 P : (σ → ℂ) → ℂ) : Germ (𝓝[X] x) ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«GermMinimalPolynomialDivides».«coe_eval₂_map» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermMinimalPolynomialDivides_coe_eval__map_ee79be857def
