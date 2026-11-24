-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAtComp_apply_7f605f1103e2
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAtComp_apply_7f605f1103e2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:33:00.96409+00:00
-- url     : https://prove2.me/theorems/45ebe572-3e7e-4bb3-9f26-cfeb23242e70
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets analytic At Comp apply 7f605f1103e2: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets ana
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets analytic At Comp apply 7f605f1103e2 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets analytic At Comp apply 7f605f1103e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/DetEqZeroOfMulVecEqZero.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/DetEqZeroOfMulVecEqZero.lean#L31-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_DetEqZeroOfMulVecEqZero
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
open Topology Filter Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAtComp_apply_7f605f1103e2 {σ τ : Type} [Fintype σ] [Fintype τ] (x : σ → ℂ)
    (L : (σ → ℂ) →L[ℂ] (τ → ℂ)) (g : analyticAtSubring (L x)) (z : σ → ℂ) :
    (analyticAtComp x L g : (σ → ℂ) → ℂ) z = (g : (τ → ℂ) → ℂ) (L z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«analyticAtComp_apply» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAtComp_apply_7f605f1103e2

attribute [defeq] P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAtComp_apply_7f605f1103e2
