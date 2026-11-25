-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_zero_ne_near_9db1a5a3b04f
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_zero_ne_near_9db1a5a3b04f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:21:01.606275+00:00
-- url     : https://prove2.me/theorems/6a44283e-2df9-4e49-a91e-f748338c3c18
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists zero ne near 9db1a5a3b04f: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists zero ne near 9db1a5a3b04f construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Complex Sets exists zero ne near 9db1a5a3b04f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/HolomorphicZerosNotIsolated.lean#L32-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/HolomorphicZerosNotIsolated.lean#L32-L152

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_zero_ne_near_9db1a5a3b04f {k : ℕ} (hk : 2 ≤ k) {J : (Fin k → ℂ) → ℂ} {c : Fin k → ℂ}
    (hJ : AnalyticAt ℂ J c) (hc : J c = 0) {W : Set (Fin k → ℂ)} (hW : W ∈ 𝓝 c) :
    ∃ z ∈ W, z ≠ c ∧ J z = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«ComplexSets».«exists_zero_ne_near» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_zero_ne_near_9db1a5a3b04f
