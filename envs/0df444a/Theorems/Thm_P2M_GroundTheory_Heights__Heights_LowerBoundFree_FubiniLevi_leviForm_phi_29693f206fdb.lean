-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_leviForm_phi_29693f206fdb
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_leviForm_phi_29693f206fdb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:45.717336+00:00
-- url     : https://prove2.me/theorems/6d1aaeac-5973-4c8b-8cdd-002968ec101f
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi levi Form phi 29693f206fdb: P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi levi Form phi 29693f206fdb
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi levi Form phi 29693f206fdb construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi levi Form phi 29693f206fdb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L97-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L97-L105

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

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_leviForm_phi_29693f206fdb {z : J → ℂ} (hz : sqSum z ≠ 0) (w : J → ℂ) :
    leviForm phi z w = (sqSum z * sqSum w - (reInner z w ^ 2 + reInner z (Complex.I • w) ^ 2)) /
      (2 * sqSum z ^ 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«FubiniLevi».«leviForm_phi» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_leviForm_phi_29693f206fdb
