-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_log_rho_eq_phi_a87fea3648ce
-- name    : P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_log_rho_eq_phi_a87fea3648ce
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:22:57.606498+00:00
-- url     : https://prove2.me/theorems/efab47ac-0e3b-4042-a58c-739f7ad928fb
-- title:
--   P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi log rho eq phi a87fea3648ce: P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi log rho eq phi a87fea3648ce
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi log rho eq phi a87fea3648ce construction uses the P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi log rho eq phi a87fea3648ce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PTorusInvLevi.lean#L131-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PTorusInvLevi.lean#L131-L135

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

theorem P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_log_rho_eq_phi_a87fea3648ce (x : J → ℂ) : Real.log ((fsMetric J).ρ x) = phi x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«TorusInvariantLevi».«log_rho_eq_phi» := P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_log_rho_eq_phi_a87fea3648ce
