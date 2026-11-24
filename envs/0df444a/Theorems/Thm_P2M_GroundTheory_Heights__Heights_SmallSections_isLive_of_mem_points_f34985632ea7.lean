-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_isLive_of_mem_points_f34985632ea7
-- name    : P2M_GroundTheory_Heights__Heights_SmallSections_isLive_of_mem_points_f34985632ea7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:20.834892+00:00
-- url     : https://prove2.me/theorems/c8adf07e-c821-48fc-93b2-da91ca135b7f
-- title:
--   P2 M Ground Theory Heights  Heights Small Sections is Live of mem points f34985632ea7: P2 M Ground Theory Heights  Heights Small Sections is Live of mem points f34985632ea7
-- statement:
--   The P2 M Ground Theory Heights  Heights Small Sections is Live of mem points f34985632ea7 construction uses the P2 M Ground Theory Heights  Heights Small Sections is Live of mem points f34985632ea7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L84-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L84-L86

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SmallSections
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_SmallSections_isLive_of_mem_points_f34985632ea7 {P : ArithVariety n} {z : Cone n ℂ} (hz : z ∈ P.points ℂ)
    {c : (k : ι) → Fin (n k + 1)} (hzc : ∀ k, z k (c k) ≠ 0) : P.IsLive c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SmallSections».«isLive_of_mem_points» := P2M_GroundTheory_Heights__Heights_SmallSections_isLive_of_mem_points_f34985632ea7
