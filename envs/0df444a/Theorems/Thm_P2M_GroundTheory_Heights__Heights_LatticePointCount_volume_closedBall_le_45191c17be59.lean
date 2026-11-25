-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticePointCount_volume_closedBall_le_45191c17be59
-- name    : P2M_GroundTheory_Heights__Heights_LatticePointCount_volume_closedBall_le_45191c17be59
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:28:09.562273+00:00
-- url     : https://prove2.me/theorems/919e9c7e-88b2-4e69-98f7-87711fa09d46
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Point Count volume closed Ball le 45191c17be59: P2 M Ground Theory Heights  Heights Lattice Point Count volume closed Ball le 45191c17be59
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Point Count volume closed Ball le 45191c17be59 construction uses the P2 M Ground Theory Heights  Heights Lattice Point Count volume closed Ball le 45191c17be59 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/VolumeFundamentalDomainEq.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/VolumeFundamentalDomainEq.lean#L12-L24

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

theorem P2M_GroundTheory_Heights__Heights_LatticePointCount_volume_closedBall_le_45191c17be59 (r : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    volume (closedBall (0 : EuclideanSpace ℝ (Fin r)) R) ≤ ENNReal.ofReal (2 * R) ^ r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticePointCount».«volume_closedBall_le» := P2M_GroundTheory_Heights__Heights_LatticePointCount_volume_closedBall_le_45191c17be59
