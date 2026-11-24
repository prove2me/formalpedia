-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_leviForm_phi_nonneg_f9953347f1be
-- name    : P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_leviForm_phi_nonneg_f9953347f1be
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:50.938309+00:00
-- url     : https://prove2.me/theorems/1a894ace-87ee-44cb-bafd-8f2e45ab71c3
-- title:
--   P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi levi Form phi nonneg f9953347f1be: P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi levi Form phi nonneg f9953347f1be
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi levi Form phi nonneg f9953347f1be construction uses the P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi levi Form phi nonneg f9953347f1be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PTorusInvLevi.lean#L65-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PTorusInvLevi.lean#L65-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTorusInvLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PTorusInvLevi
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi
set_option linter.unusedSectionVars false
variable {J : Type} [Fintype J]

theorem P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_leviForm_phi_nonneg_f9953347f1be {z : J → ℂ} (hS : sqSum z ≠ 0) (w : J → ℂ) : 0 ≤ leviForm phi z w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«TorusInvariantLevi».«leviForm_phi_nonneg» := P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_leviForm_phi_nonneg_f9953347f1be
