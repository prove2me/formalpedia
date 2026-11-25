-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_differentiableAt_coeff_prod_974a041f6356
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_differentiableAt_coeff_prod_974a041f6356
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:21:06.333501+00:00
-- url     : https://prove2.me/theorems/e896abd0-785e-4a79-8077-cac03f80f816
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Polynomial Root Predicate Factor differentiable At coeff prod 974a041f6356: P2 M Ground Theory Heights  Heights Indefini
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Polynomial Root Predicate Factor differentiable At coeff prod 974a041f6356 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Polynomial Root Predicate Factor differentiable At coeff prod 974a041f6356 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPolynomialRootPredicateFactor.lean#L97-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPolynomialRootPredicateFactor.lean#L97-L111

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_differentiableAt_coeff_prod_974a041f6356 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (F : Multiset ℂ)
    (g : ℂ → E → ℂ) (x : E) (hg : ∀ τ, DifferentiableAt ℂ (g τ) x) :
    ∀ k : ℕ, DifferentiableAt ℂ (fun s => ((F.map fun τ => X - C (g τ s)).prod).coeff k) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«PolynomialRootPredicateFactor».«differentiableAt_coeff_prod» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_differentiableAt_coeff_prod_974a041f6356
