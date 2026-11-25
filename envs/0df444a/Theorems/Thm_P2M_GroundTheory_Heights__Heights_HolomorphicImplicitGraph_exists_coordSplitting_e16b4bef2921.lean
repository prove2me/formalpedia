-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HolomorphicImplicitGraph_exists_coordSplitting_e16b4bef2921
-- name    : P2M_GroundTheory_Heights__Heights_HolomorphicImplicitGraph_exists_coordSplitting_e16b4bef2921
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:20:57.079722+00:00
-- url     : https://prove2.me/theorems/7a5e7c7a-16b8-5179-ac36-4aa7097f82f7
-- title:
--   P2 M Ground Theory Heights  Heights Holomorphic Implicit Graph exists coord Splitting e16b4bef2921: P2 M Ground Theory Heights  Heights Holomorphic Implicit Graph exists coord Splitting e16b4bef2921
-- statement:
--   The P2 M Ground Theory Heights  Heights Holomorphic Implicit Graph exists coord Splitting e16b4bef2921 construction uses the P2 M Ground Theory Heights  Heights Holomorphic Implicit Graph exists coord Splitting e16b4bef2921 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PHolomorphicImplicitGraph.lean#L13-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PHolomorphicImplicitGraph.lean#L13-L66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsHolomorphicImplicitGraph
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PHolomorphicImplicitGraph
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Module Function
noncomputable section
open GroundTheory.Heights₂.Heights.HolomorphicImplicitGraph

theorem P2M_GroundTheory_Heights__Heights_HolomorphicImplicitGraph_exists_coordSplitting_e16b4bef2921 {n m : ℕ} (L : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin (n - m) → ℂ))
    (hL : finrank ℂ (LinearMap.ker L) = m) :
    ∃ e : Fin n ≃ Fin m ⊕ Fin (n - m), ∀ v : EuclideanSpace ℂ (Fin n),
      (∀ j k, e j = Sum.inl k → v j = 0) → L v = 0 → v = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HolomorphicImplicitGraph».«exists_coordSplitting» := P2M_GroundTheory_Heights__Heights_HolomorphicImplicitGraph_exists_coordSplitting_e16b4bef2921
