-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicZeroSetDimH_dimH_regular_zeros_le_092cf97b9ce1
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicZeroSetDimH_dimH_regular_zeros_le_092cf97b9ce1
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:20:54.693807+00:00
-- url     : https://prove2.me/theorems/a429518b-f588-4943-bd26-16a54bb46301
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Holomorphic Zero Set Dim H dim H regular zeros le 092cf97b9ce1: P2 M Ground Theory Heights  Heights Indefinite Row Side
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Holomorphic Zero Set Dim H dim H regular zeros le 092cf97b9ce1 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Holomorphic Zero Set Dim H dim H regular zeros le 092cf97b9ce1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHolomorphicZeroSetDimH.lean#L38-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHolomorphicZeroSetDimH.lean#L38-L51

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicZeroSetDimH_dimH_regular_zeros_le_092cf97b9ce1 {k : ℕ} {U : Set (Fin k → ℂ)} {g : (Fin k → ℂ) → ℂ}
    (hg : AnalyticOnNhd ℂ g U) :
    dimH {v | v ∈ U ∧ g v = 0 ∧ fderiv ℂ g v ≠ 0} ≤ 2 * ((k - 1 : ℕ) : ℝ≥0∞) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«HolomorphicZeroSetDimH».«dimH_regular_zeros_le» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicZeroSetDimH_dimH_regular_zeros_le_092cf97b9ce1
