-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_hasFDerivAt_sqSum_43e986969273
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_hasFDerivAt_sqSum_43e986969273
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:34:27.521578+00:00
-- url     : https://prove2.me/theorems/4212ca1e-79be-44ac-9cb5-5e7664e8fbee
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi has FDeriv At sq Sum 43e986969273: P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi has FDeriv At sq Sum 43e986969273
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi has FDeriv At sq Sum 43e986969273 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi has FDeriv At sq Sum 43e986969273 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L39-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L39-L51

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

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_hasFDerivAt_sqSum_43e986969273 (z : J → ℂ) : HasFDerivAt sqSum ((2 : ℝ) • reInner z) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«FubiniLevi».«hasFDerivAt_sqSum» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_hasFDerivAt_sqSum_43e986969273
