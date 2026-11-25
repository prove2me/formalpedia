-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ParametricCircleIntegralAnalytic_analyticOnNhd_of_differentiableOn_fd_37006865feb4
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ParametricCircleIntegralAnalytic_analyticOnNhd_of_differentiableOn_fd_37006865feb4
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:20:41.052429+00:00
-- url     : https://prove2.me/theorems/a1de2039-e818-46fc-a2e5-6d3189c1f5be
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Parametric Circle Integral Analytic analytic On Nhd of differentiable On fd 37006865feb4: P2 M Ground Theory Heights  He
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Parametric Circle Integral Analytic analytic On Nhd of differentiable On fd 37006865feb4 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Parametric Circle Integral Analytic analytic On Nhd of differentiable On fd 37006865feb4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PParametricCircleIntegralAnalytic.lean#L16-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PParametricCircleIntegralAnalytic.lean#L16-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametricCircleIntegralAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PParametricCircleIntegralAnalytic
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
open Metric Filter Topology Set Complex MeasureTheory
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.ParametricCircleIntegralAnalytic

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ParametricCircleIntegralAnalytic_analyticOnNhd_of_differentiableOn_fd_37006865feb4 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {O : Set E} {f : E → ℂ} (hO : IsOpen O) (hf : DifferentiableOn ℂ f O) :
    AnalyticOnNhd ℂ f O := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«ParametricCircleIntegralAnalytic».«analyticOnNhd_of_differentiableOn_fd» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_ParametricCircleIntegralAnalytic_analyticOnNhd_of_differentiableOn_fd_37006865feb4
