-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_hasFDerivAt_phi_3584397ba630
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_hasFDerivAt_phi_3584397ba630
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:30:19.680627+00:00
-- url     : https://prove2.me/theorems/9387cda1-d74c-4c44-8a0f-8d68c4f18211
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi has FDeriv At phi 3584397ba630: P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi has FDeriv At phi 3584397ba630
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi has FDeriv At phi 3584397ba630 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi has FDeriv At phi 3584397ba630 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L55-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L55-L61

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

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_hasFDerivAt_phi_3584397ba630 {z : J → ℂ} (hz : sqSum z ≠ 0) :
    HasFDerivAt phi ((sqSum z)⁻¹ • reInner z) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«FubiniLevi».«hasFDerivAt_phi» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_hasFDerivAt_phi_3584397ba630
