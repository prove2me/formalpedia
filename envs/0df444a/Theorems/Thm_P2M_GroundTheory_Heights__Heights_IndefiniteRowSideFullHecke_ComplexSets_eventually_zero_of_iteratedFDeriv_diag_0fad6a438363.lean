-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eventually_zero_of_iteratedFDeriv_diag_0fad6a438363
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eventually_zero_of_iteratedFDeriv_diag_0fad6a438363
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:21:11.880729+00:00
-- url     : https://prove2.me/theorems/86a644b1-542c-43a5-b731-d2624c8d737e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eventually zero of iterated FDeriv diag 0fad6a438363: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eventually zero of iterated FDeriv diag 0fad6a438363 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets eventually zero of iterated FDeriv diag 0fad6a438363 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegularLocusDense.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegularLocusDense.lean#L15-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularLocusDense
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticImplicitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularLocusDense
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
open Topology Filter Module
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eventually_zero_of_iteratedFDeriv_diag_0fad6a438363 {ψ : E → ℂ} {y₀ : E} (hψ : AnalyticAt ℂ ψ y₀)
    (h0 : ∀ (n : ℕ) (v : E), iteratedFDeriv ℂ n ψ y₀ (fun _ => v) = 0) :
    ∀ᶠ u in 𝓝 y₀, ψ u = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«eventually_zero_of_iteratedFDeriv_diag» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_eventually_zero_of_iteratedFDeriv_diag_0fad6a438363
