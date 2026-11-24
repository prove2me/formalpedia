-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_logh_contDiffAt_620c52edbdfa
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_logh_contDiffAt_620c52edbdfa
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:14.72573+00:00
-- url     : https://prove2.me/theorems/756c1ff2-20ca-455f-a1a2-3235a97e60fb
-- title:
--   P2 M Ground Theory Heights  Heights Inter point Form Euler holds logh cont Diff At 620c52edbdfa: P2 M Ground Theory Heights  Heights Inter point Form Euler holds logh cont Diff At 620c52edbdfa
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter point Form Euler holds logh cont Diff At 620c52edbdfa construction uses the P2 M Ground Theory Heights  Heights Inter point Form Euler holds logh cont Diff At 620c52edbdfa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LeviOfRealSmulRight.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LeviOfRealSmulRight.lean#L78-L81

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

theorem P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_logh_contDiffAt_620c52edbdfa {A : HermLine ι} (hA : IsSmoothHerm A) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContDiffAt ℝ 2 (fun z' => Real.log (A.h z')) z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pointFormEuler_holds».«logh_contDiffAt» := P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_logh_contDiffAt_620c52edbdfa
