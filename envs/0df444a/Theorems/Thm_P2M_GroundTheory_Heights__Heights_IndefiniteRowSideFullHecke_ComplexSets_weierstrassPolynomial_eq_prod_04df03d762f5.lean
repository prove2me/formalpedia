-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassPolynomial_eq_prod_04df03d762f5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassPolynomial_eq_prod_04df03d762f5
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:21:36.44121+00:00
-- url     : https://prove2.me/theorems/4776d0d5-0852-4a9a-8c20-e2f1bd7fc652
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets weierstrass Polynomial eq prod 04df03d762f5: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets weierstrass Polynomial eq prod 04df03d762f5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets weierstrass Polynomial eq prod 04df03d762f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermWeierstrassPreparation.lean#L45-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PGermWeierstrassPreparation.lean#L45-L65

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassPreparation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametricCircleIntegralAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCircleArgumentPrinciple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPowerSumsEsymmAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermWeierstrassPreparation
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
open Topology Filter Metric Complex Real
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassPolynomial_eq_prod_04df03d762f5 {σ : Type} {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ) (z : σ → ℂ)
    (Z : Multiset ℂ) (hZ : Multiset.card Z = d)
    (hc : ∀ j : Fin d, c j z = (-1) ^ (d - (j : ℕ)) * Z.esymm (d - (j : ℕ))) (t : ℂ) :
    weierstrassPolynomial c (pointWithLast z t) = (Z.map fun a => t - a).prod := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«weierstrassPolynomial_eq_prod» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_weierstrassPolynomial_eq_prod_04df03d762f5
