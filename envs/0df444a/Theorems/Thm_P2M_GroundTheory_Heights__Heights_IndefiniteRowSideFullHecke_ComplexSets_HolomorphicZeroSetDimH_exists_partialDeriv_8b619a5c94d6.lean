-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicZeroSetDimH_exists_partialDeriv_8b619a5c94d6
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicZeroSetDimH_exists_partialDeriv_8b619a5c94d6
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:20:19.770294+00:00
-- url     : https://prove2.me/theorems/b9338868-b4a4-5dd9-9210-c968eaa598a8
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Holomorphic Zero Set Dim H exists partial Deriv 8b619a5c94d6: P2 M Ground Theory Heights  Heights Indefinite Row Side Fu
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Holomorphic Zero Set Dim H exists partial Deriv 8b619a5c94d6 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets Holomorphic Zero Set Dim H exists partial Deriv 8b619a5c94d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHolomorphicZeroSetDimH.lean#L53-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHolomorphicZeroSetDimH.lean#L53-L88

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicZeroSetDimH_exists_partialDeriv_8b619a5c94d6 {k : ℕ} {U : Set (Fin k → ℂ)} {h : (Fin k → ℂ) → ℂ} (hU : IsOpen U)
    (hh : AnalyticOnNhd ℂ h U) (hW : ∀ W ⊆ U, IsOpen W → W.Nonempty → ∃ w ∈ W, h w ≠ 0)
    {v : Fin k → ℂ} (hv : v ∈ U) (h0 : h v = 0) :
    ∃ n m, partialDeriv h n m v = 0 ∧ fderiv ℂ (partialDeriv h n m) v ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«HolomorphicZeroSetDimH».«exists_partialDeriv» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicZeroSetDimH_exists_partialDeriv_8b619a5c94d6
