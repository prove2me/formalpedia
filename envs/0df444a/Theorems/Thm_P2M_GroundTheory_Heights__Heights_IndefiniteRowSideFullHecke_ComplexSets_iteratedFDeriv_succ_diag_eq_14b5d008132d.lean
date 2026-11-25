-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_iteratedFDeriv_succ_diag_eq_14b5d008132d
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_iteratedFDeriv_succ_diag_eq_14b5d008132d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:21:19.134542+00:00
-- url     : https://prove2.me/theorems/b7fad0c2-a205-4f94-9bff-13fc889cfdc5
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets iterated FDeriv succ diag eq 14b5d008132d: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Se
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets iterated FDeriv succ diag eq 14b5d008132d construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets iterated FDeriv succ diag eq 14b5d008132d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegularLocusDense.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PRegularLocusDense.lean#L26-L34

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_iteratedFDeriv_succ_diag_eq_14b5d008132d {ψ : E → ℂ} {y₀ : E} (hψ : AnalyticAt ℂ ψ y₀) (n : ℕ) (v : E) :
    iteratedFDeriv ℂ (n + 1) ψ y₀ (fun _ => v) =
      iteratedFDeriv ℂ n (fun y => fderiv ℂ ψ y v) y₀ (fun _ => v) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«iteratedFDeriv_succ_diag_eq» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_iteratedFDeriv_succ_diag_eq_14b5d008132d
