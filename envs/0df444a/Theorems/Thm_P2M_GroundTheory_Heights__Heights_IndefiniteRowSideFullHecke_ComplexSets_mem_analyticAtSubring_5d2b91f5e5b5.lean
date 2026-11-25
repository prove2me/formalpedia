-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_analyticAtSubring_5d2b91f5e5b5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_analyticAtSubring_5d2b91f5e5b5
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:21:33.281481+00:00
-- url     : https://prove2.me/theorems/1a9f4429-c06d-4ea1-b7b2-6cfbde1383ca
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets mem analytic At Subring 5d2b91f5e5b5: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets me
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets mem analytic At Subring 5d2b91f5e5b5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets mem analytic At Subring 5d2b91f5e5b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/DetEqZeroOfMulVecEqZero.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/DetEqZeroOfMulVecEqZero.lean#L19-L21

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_analyticAtSubring_5d2b91f5e5b5 {σ : Type} [Fintype σ] {p : σ → ℂ} {g : (σ → ℂ) → ℂ} :
    g ∈ analyticAtSubring p ↔ AnalyticAt ℂ g p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«mem_analyticAtSubring» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_mem_analyticAtSubring_5d2b91f5e5b5
