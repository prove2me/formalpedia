-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicZeroSetDimH_dimH_image_le_of_analyticOnNhd_2f93c902b017
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicZeroSetDimH_dimH_image_le_of_analyticOnNhd_2f93c902b017
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:20:19.067957+00:00
-- url     : https://prove2.me/theorems/84823d34-c6b3-5bca-8253-b1b53d490a7d
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Holomorphic Zero Set Dim H dim H image le of analytic On Nhd 2f93c902b017: P2 M Ground Theory Heights  Heights Indefinit
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Holomorphic Zero Set Dim H dim H image le of analytic On Nhd 2f93c902b017 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Holomorphic Zero Set Dim H dim H image le of analytic On Nhd 2f93c902b017 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHolomorphicZeroSetDimH.lean#L26-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHolomorphicZeroSetDimH.lean#L26-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicZeroSetDimH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticImplicitChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PProperHolomorphicSurjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHolomorphicZeroSetDimH
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
open Topology Metric Filter
open scoped ENNReal NNReal
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.HolomorphicZeroSetDimH

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicZeroSetDimH_dimH_image_le_of_analyticOnNhd_2f93c902b017 {d : ℕ} {σ : Type*} [Fintype σ] {O : Set (Fin d → ℂ)}
    {g : (Fin d → ℂ) → σ → ℂ} (hg : AnalyticOnNhd ℂ g O) : dimH (g '' O) ≤ 2 * (d : ℝ≥0∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«HolomorphicZeroSetDimH».«dimH_image_le_of_analyticOnNhd» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicZeroSetDimH_dimH_image_le_of_analyticOnNhd_2f93c902b017
