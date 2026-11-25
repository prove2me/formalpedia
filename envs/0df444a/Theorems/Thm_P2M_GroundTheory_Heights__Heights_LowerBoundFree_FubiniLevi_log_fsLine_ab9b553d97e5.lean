-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_log_fsLine_ab9b553d97e5
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_log_fsLine_ab9b553d97e5
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:29:03.195382+00:00
-- url     : https://prove2.me/theorems/e258c93e-b97a-4eed-bb62-9d88cd53abda
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi log fs Line ab9b553d97e5: P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi log fs Line ab9b553d97e5
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi log fs Line ab9b553d97e5 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi log fs Line ab9b553d97e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L153-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L153-L159

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

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_log_fsLine_ab9b553d97e5 (z : (Σ _ : Unit, Fin 2) → ℂ) : Real.log ((fsLine 2).h z) = phi z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«FubiniLevi».«log_fsLine» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_log_fsLine_ab9b553d97e5
