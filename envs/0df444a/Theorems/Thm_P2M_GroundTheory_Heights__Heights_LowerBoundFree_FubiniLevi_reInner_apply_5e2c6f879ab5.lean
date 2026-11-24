-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_reInner_apply_5e2c6f879ab5
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_reInner_apply_5e2c6f879ab5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:42.014826+00:00
-- url     : https://prove2.me/theorems/fc0e27c7-d1e0-4b90-ba09-c06f113ed166
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi re Inner apply 5e2c6f879ab5: P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi re Inner apply 5e2c6f879ab5
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi re Inner apply 5e2c6f879ab5 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi re Inner apply 5e2c6f879ab5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L19-L21

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

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_reInner_apply_5e2c6f879ab5 (a b : J → ℂ) :
    reInner a b = ∑ p, ((a p).re * (b p).re + (a p).im * (b p).im) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«FubiniLevi».«reInner_apply» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_reInner_apply_5e2c6f879ab5
