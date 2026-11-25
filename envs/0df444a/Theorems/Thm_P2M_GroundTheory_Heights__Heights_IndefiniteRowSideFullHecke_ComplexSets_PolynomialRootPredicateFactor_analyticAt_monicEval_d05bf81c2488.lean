-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_analyticAt_monicEval_d05bf81c2488
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_analyticAt_monicEval_d05bf81c2488
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:20:26.484578+00:00
-- url     : https://prove2.me/theorems/73db4956-6f16-4c90-80ea-a34401d3c205
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Polynomial Root Predicate Factor analytic At monic Eval d05bf81c2488: P2 M Ground Theory Heights  Heights Indefinite Row
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Polynomial Root Predicate Factor analytic At monic Eval d05bf81c2488 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Polynomial Root Predicate Factor analytic At monic Eval d05bf81c2488 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPolynomialRootPredicateFactor.lean#L267-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPolynomialRootPredicateFactor.lean#L267-L272

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_analyticAt_monicEval_d05bf81c2488 {d m : ℕ} (F : ℕ → (Fin d → ℂ) → ℂ) (t : Fin d → ℂ) (T : ℂ)
    (hF : ∀ k, AnalyticAt ℂ (F k) t) :
    AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => u.2 ^ m + ∑ k ∈ Finset.range m, F k u.1 * u.2 ^ k) (t, T) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«PolynomialRootPredicateFactor».«analyticAt_monicEval» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_PolynomialRootPredicateFactor_analyticAt_monicEval_d05bf81c2488
