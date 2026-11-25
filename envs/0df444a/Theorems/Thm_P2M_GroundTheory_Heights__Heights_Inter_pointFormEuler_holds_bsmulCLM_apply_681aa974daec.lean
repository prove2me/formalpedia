-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_bsmulCLM_apply_681aa974daec
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_bsmulCLM_apply_681aa974daec
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:35:22.040371+00:00
-- url     : https://prove2.me/theorems/70fbe669-6698-5d46-8231-422016b356fd
-- title:
--   P2 M Ground Theory Heights  Heights Inter point Form Euler holds bsmul CLM apply 681aa974daec: P2 M Ground Theory Heights  Heights Inter point Form Euler holds bsmul CLM apply 681aa974daec
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter point Form Euler holds bsmul CLM apply 681aa974daec construction uses the P2 M Ground Theory Heights  Heights Inter point Form Euler holds bsmul CLM apply 681aa974daec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LeviOfRealSmulRight.lean#L87-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LeviOfRealSmulRight.lean#L87-L89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LeviOfRealSmulRight
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
open Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_bsmulCLM_apply_681aa974daec (d : K → ℂ) (z : (Σ k, ι k) → ℂ) : bsmulCLM d z = bsmul d z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pointFormEuler_holds».«bsmulCLM_apply» := P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_bsmulCLM_apply_681aa974daec
