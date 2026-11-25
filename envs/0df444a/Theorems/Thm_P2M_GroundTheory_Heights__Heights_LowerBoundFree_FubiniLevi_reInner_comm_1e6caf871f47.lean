-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_reInner_comm_1e6caf871f47
-- name    : P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_reInner_comm_1e6caf871f47
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:24.056571+00:00
-- url     : https://prove2.me/theorems/21fb7dc0-9592-419e-b084-e0c10e08fc9e
-- title:
--   P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi re Inner comm 1e6caf871f47: P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi re Inner comm 1e6caf871f47
-- statement:
--   The P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi re Inner comm 1e6caf871f47 construction uses the P2 M Ground Theory Heights  Heights Lower Bound Free Fubini Levi re Inner comm 1e6caf871f47 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L23-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/CoordinateIdeals/FubiniLevi.lean#L23-L25

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

theorem P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_reInner_comm_1e6caf871f47 (a b : J → ℂ) : reInner a b = reInner b a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LowerBoundFree».«FubiniLevi».«reInner_comm» := P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_reInner_comm_1e6caf871f47
