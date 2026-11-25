-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_reInner_self_1b2324488aab
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_reInner_self_1b2324488aab
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:28:04.833227+00:00
-- url     : https://prove2.me/theorems/af0e0430-03dd-43d3-b988-65b3d75ca700
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi re Inner self 1b2324488aab: P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi re Inner self 1b2324488aab
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi re Inner self 1b2324488aab construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi re Inner self 1b2324488aab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L27-L30

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

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_reInner_self_1b2324488aab (a : J → ℂ) : reInner a a = sqSum a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«FubiniLevi».«reInner_self» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_reInner_self_1b2324488aab
