-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticePointCount_card_mul_volume_le_d74be91004af
-- name    : P2M_GroundTheory_Heights__Heights_LatticePointCount_card_mul_volume_le_d74be91004af
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:29:10.727418+00:00
-- url     : https://prove2.me/theorems/0f076691-d289-4de6-b8b8-b74782f89cf9
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Point Count card mul volume le d74be91004af: P2 M Ground Theory Heights  Heights Lattice Point Count card mul volume le d74be91004af
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Point Count card mul volume le d74be91004af construction uses the P2 M Ground Theory Heights  Heights Lattice Point Count card mul volume le d74be91004af property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/VolumeFundamentalDomainEq.lean#L26-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/VolumeFundamentalDomainEq.lean#L26-L76

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

theorem P2M_GroundTheory_Heights__Heights_LatticePointCount_card_mul_volume_le_d74be91004af {r : ℕ} (c : Basis (Fin r) ℝ (EuclideanSpace ℝ (Fin r))) {μ : ℝ}
    (hcov : ∀ y, ∃ l ∈ span ℤ (Set.range c), ‖y - l‖ ≤ μ)
    (X : Finset (EuclideanSpace ℝ (Fin r)))
    (hX : ∀ x ∈ X, x ∈ span ℤ (Set.range c) ∧ ‖x‖ ≤ 1) :
    (X.card : ℝ≥0∞) * volume (ZSpan.fundamentalDomain c) ≤
      volume (closedBall (0 : EuclideanSpace ℝ (Fin r)) (1 + μ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticePointCount».«card_mul_volume_le» := P2M_GroundTheory_Heights__Heights_LatticePointCount_card_mul_volume_le_d74be91004af
