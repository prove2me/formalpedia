-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_contDiffAt_phi_ce22939b8b91
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_contDiffAt_phi_ce22939b8b91
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:29.369889+00:00
-- url     : https://prove2.me/theorems/058ec5dc-9cf0-4291-9abb-d984679942b9
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi cont Diff At phi ce22939b8b91: P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi cont Diff At phi ce22939b8b91
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi cont Diff At phi ce22939b8b91 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi cont Diff At phi ce22939b8b91 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L63-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L63-L67

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

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_contDiffAt_phi_ce22939b8b91 {z : J → ℂ} (hz : sqSum z ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n phi z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«FubiniLevi».«contDiffAt_phi» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_contDiffAt_phi_ce22939b8b91
