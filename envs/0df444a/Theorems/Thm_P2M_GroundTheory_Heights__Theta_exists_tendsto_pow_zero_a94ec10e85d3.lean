-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_exists_tendsto_pow_zero_a94ec10e85d3
-- name    : P2M_GroundTheory_Heights__Theta_exists_tendsto_pow_zero_a94ec10e85d3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:54.333899+00:00
-- url     : https://prove2.me/theorems/1c62e9f7-8a5c-4f06-b96b-241fd44bb921
-- title:
--   P2 M Ground Theory Heights  Theta exists tendsto pow zero a94ec10e85d3: P2 M Ground Theory Heights  Theta exists tendsto pow zero a94ec10e85d3
-- statement:
--   The P2 M Ground Theory Heights  Theta exists tendsto pow zero a94ec10e85d3 construction uses the P2 M Ground Theory Heights  Theta exists tendsto pow zero a94ec10e85d3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/LocallyCompactField/Countability.lean#L47-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/LocallyCompactField/Countability.lean#L47-L159

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LocallyCompactField_Countability
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open MeasureTheory Measure Filter Topology Set
open scoped NNReal ENNReal Pointwise
variable {R : Type*} [Field R] [TopologicalSpace R] [IsTopologicalRing R]
variable [LocallyCompactSpace R] [T2Space R]

theorem P2M_GroundTheory_Heights__Theta_exists_tendsto_pow_zero_a94ec10e85d3 (hR : ¬ DiscreteTopology R) :
    ∃ t : R, t ≠ 0 ∧ Tendsto (fun n : ℕ => t ^ n) atTop (𝓝 0) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«exists_tendsto_pow_zero» := P2M_GroundTheory_Heights__Theta_exists_tendsto_pow_zero_a94ec10e85d3
