-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_eventually_mul_mem_of_isCompact_2b6e19c23fce
-- name    : P2M_GroundTheory_Heights__Theta_eventually_mul_mem_of_isCompact_2b6e19c23fce
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:57.216483+00:00
-- url     : https://prove2.me/theorems/d4926e23-f113-4457-b8d4-3eb7baaa1493
-- title:
--   P2 M Ground Theory Heights  Theta eventually mul mem of is Compact 2b6e19c23fce: P2 M Ground Theory Heights  Theta eventually mul mem of is Compact 2b6e19c23fce
-- statement:
--   The P2 M Ground Theory Heights  Theta eventually mul mem of is Compact 2b6e19c23fce construction uses the P2 M Ground Theory Heights  Theta eventually mul mem of is Compact 2b6e19c23fce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/LocallyCompactField/Countability.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/LocallyCompactField/Countability.lean#L36-L43

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

theorem P2M_GroundTheory_Heights__Theta_eventually_mul_mem_of_isCompact_2b6e19c23fce {K N : Set R} (hK : IsCompact K) (hN : N ∈ 𝓝 (0 : R)) :
    ∀ᶠ u in 𝓝 (0 : R), ∀ w ∈ K, u * w ∈ N := by sorry

alias «GroundTheory».«Heights₂».«Theta».«eventually_mul_mem_of_isCompact» := P2M_GroundTheory_Heights__Theta_eventually_mul_mem_of_isCompact_2b6e19c23fce
