-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticePointCount_exists_near_9e6247090531
-- name    : P2M_GroundTheory_Heights__Heights_LatticePointCount_exists_near_9e6247090531
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:59.430737+00:00
-- url     : https://prove2.me/theorems/dfe1ae21-28c9-43d5-9c1d-be2254ec48d8
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Point Count exists near 9e6247090531: P2 M Ground Theory Heights  Heights Lattice Point Count exists near 9e6247090531
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Point Count exists near 9e6247090531 construction uses the P2 M Ground Theory Heights  Heights Lattice Point Count exists near 9e6247090531 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/VolumeFundamentalDomainEq.lean#L98-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/VolumeFundamentalDomainEq.lean#L98-L143

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_VolumeFundamentalDomainEq
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
open MeasureTheory Metric Module Submodule
open scoped ENNReal Pointwise
open GroundTheory.Heights₂.Heights.LatticePointCount

theorem P2M_GroundTheory_Heights__Heights_LatticePointCount_exists_near_9e6247090531 {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {r : ℕ} (b : Fin r → V)
    (hb : LinearIndependent ℝ b) (S : Set V) (C : ℝ) (hS : ∀ s ∈ S, ‖s‖ ≤ C)
    (hspan : span ℤ S = span ℤ (Set.range b)) (v : V) (hv : v ∈ span ℝ (Set.range b)) :
    ∃ l ∈ span ℤ (Set.range b), ‖v - l‖ ≤ r * C := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticePointCount».«exists_near» := P2M_GroundTheory_Heights__Heights_LatticePointCount_exists_near_9e6247090531
