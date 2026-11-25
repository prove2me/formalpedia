-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_continuous_sqSum_68d304758819
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_continuous_sqSum_68d304758819
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:31:00.41191+00:00
-- url     : https://prove2.me/theorems/24fac253-ca0c-41a9-a8a3-396d33a56649
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi continuous sq Sum 68d304758819: P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi continuous sq Sum 68d304758819
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi continuous sq Sum 68d304758819 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi continuous sq Sum 68d304758819 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L35-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L35-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
variable {J : Type} [Fintype J]

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_continuous_sqSum_68d304758819 : Continuous (sqSum : (J → ℂ) → ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«FubiniLevi».«continuous_sqSum» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_continuous_sqSum_68d304758819
