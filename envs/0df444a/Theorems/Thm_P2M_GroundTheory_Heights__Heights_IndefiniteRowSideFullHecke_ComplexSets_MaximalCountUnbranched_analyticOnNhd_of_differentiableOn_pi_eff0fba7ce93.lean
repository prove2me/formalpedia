-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_MaximalCountUnbranched_analyticOnNhd_of_differentiableOn_pi_eff0fba7ce93
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_MaximalCountUnbranched_analyticOnNhd_of_differentiableOn_pi_eff0fba7ce93
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:26.265552+00:00
-- url     : https://prove2.me/theorems/1ad20534-e9dd-40f7-ad2e-879ca8f4a37e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Maximal Count Unbranched analytic On Nhd of differentiable On pi eff0fba7ce93: P2 M Ground Theory Heights  Heights Indef
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Maximal Count Unbranched analytic On Nhd of differentiable On pi eff0fba7ce93 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Maximal Count Unbranched analytic On Nhd of differentiable On pi eff0fba7ce93 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaximalCountUnbranched.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMaximalCountUnbranched.lean#L13-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StMaximalCountUnbranched
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_OsgoodSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMaximalCountUnbranched
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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.MaximalCountUnbranched

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_MaximalCountUnbranched_analyticOnNhd_of_differentiableOn_pi_eff0fba7ce93 {d : ℕ} {σ : Type} [Fintype σ] {U : Set (Fin d → ℂ)}
    {G : (Fin d → ℂ) → σ → ℂ} (hU : IsOpen U) (hG : DifferentiableOn ℂ G U) : AnalyticOnNhd ℂ G U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«MaximalCountUnbranched».«analyticOnNhd_of_differentiableOn_pi» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_MaximalCountUnbranched_analyticOnNhd_of_differentiableOn_pi_eff0fba7ce93
