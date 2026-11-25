-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_finite_lattice_closedBall_e6af14f7c688
-- name    : P2M_GroundTheory_Heights__Heights_finite_lattice_closedBall_e6af14f7c688
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T06:23:48.339095+00:00
-- url     : https://prove2.me/theorems/191fb41f-253a-4517-a5dc-07707befb59e
-- title:
--   P2 M Ground Theory Heights  Heights finite lattice closed Ball e6af14f7c688: P2 M Ground Theory Heights  Heights finite lattice closed Ball e6af14f7c688
-- statement:
--   The P2 M Ground Theory Heights  Heights finite lattice closed Ball e6af14f7c688 construction uses the P2 M Ground Theory Heights  Heights finite lattice closed Ball e6af14f7c688 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/CovolumeCount.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/CovolumeCount.lean#L17-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Covolume
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Metric Module ZSpan NumberField
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (L : Submodule ℤ V) [DiscreteTopology L]
omit [MeasurableSpace V] [BorelSpace V]

theorem P2M_GroundTheory_Heights__Heights_finite_lattice_closedBall_e6af14f7c688 (r : ℝ) : {x : V | x ∈ L ∧ ‖x‖ ≤ r}.Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«finite_lattice_closedBall» := P2M_GroundTheory_Heights__Heights_finite_lattice_closedBall_e6af14f7c688
