-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_clm_apply_eq_sum_87e002e356bd
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_clm_apply_eq_sum_87e002e356bd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:21:13.135563+00:00
-- url     : https://prove2.me/theorems/92512930-7c99-4c91-aeba-7fa1831190f4
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets clm apply eq sum 87e002e356bd: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets clm apply
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets clm apply eq sum 87e002e356bd construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets clm apply eq sum 87e002e356bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitivePresentationCover.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PPrimitivePresentationCover.lean#L31-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimitivePresentationCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSeparateWeierstrassDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PevEqZeroOfPresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PPrimitivePresentationCover
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_clm_apply_eq_sum_87e002e356bd {σ : Type} [Fintype σ] [DecidableEq σ] (lam : (σ → ℂ) →L[ℂ] ℂ) (x : σ → ℂ) :
    lam x = ∑ m, x m * lam (fun j => if m = j then 1 else 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«clm_apply_eq_sum» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_clm_apply_eq_sum_87e002e356bd
