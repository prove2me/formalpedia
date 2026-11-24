-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAt_det_fderiv_e2dfa5ad9526
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAt_det_fderiv_e2dfa5ad9526
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:49:21.953305+00:00
-- url     : https://prove2.me/theorems/9efaf0b0-3f75-4d34-92d2-da7187226efc
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets analytic At det fderiv e2dfa5ad9526: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets ana
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets analytic At det fderiv e2dfa5ad9526 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets analytic At det fderiv e2dfa5ad9526 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/HolomorphicZerosNotIsolated.lean#L9-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/HolomorphicZerosNotIsolated.lean#L9-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermFiniteProjection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_HolomorphicZerosNotIsolated
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
open Topology Filter Metric

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAt_det_fderiv_e2dfa5ad9526 {k : ℕ} {f : (Fin k → ℂ) → Fin k → ℂ} {x : Fin k → ℂ}
    (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (fun z => LinearMap.det (fderiv ℂ f z : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«analyticAt_det_fderiv» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAt_det_fderiv_e2dfa5ad9526
