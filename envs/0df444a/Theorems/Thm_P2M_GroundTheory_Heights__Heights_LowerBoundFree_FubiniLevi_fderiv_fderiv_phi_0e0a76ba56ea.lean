-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_fderiv_fderiv_phi_0e0a76ba56ea
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_fderiv_fderiv_phi_0e0a76ba56ea
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:42:58.106181+00:00
-- url     : https://prove2.me/theorems/d19751f2-3002-5885-8e0a-dd35f4d0173b
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi fderiv fderiv phi 0e0a76ba56ea: P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi fderiv fderiv phi 0e0a76ba56ea
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi fderiv fderiv phi 0e0a76ba56ea construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi fderiv fderiv phi 0e0a76ba56ea property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L69-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L69-L95

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

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_fderiv_fderiv_phi_0e0a76ba56ea {z : J → ℂ} (hz : sqSum z ≠ 0) (u : J → ℂ) :
    fderiv ℝ (fderiv ℝ phi) z u u =
      sqSum u / sqSum z - 2 * reInner z u ^ 2 / sqSum z ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«FubiniLevi».«fderiv_fderiv_phi» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_fderiv_fderiv_phi_0e0a76ba56ea
