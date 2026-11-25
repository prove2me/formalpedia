-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_levi_add_sum_b89c89512e17
-- name    : P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_levi_add_sum_b89c89512e17
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:23:14.723842+00:00
-- url     : https://prove2.me/theorems/0087a609-3099-4367-9ea8-4d9d6fa3e5c0
-- title:
--   P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi levi add sum b89c89512e17: P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi levi add sum b89c89512e17
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi levi add sum b89c89512e17 construction uses the P2 M Ground Theory Heights  Heights Inter Torus Invariant Levi levi add sum b89c89512e17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PTorusInvLevi.lean#L137-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PTorusInvLevi.lean#L137-L152

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

theorem P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_levi_add_sum_b89c89512e17 {K : Type} {z : J → ℂ} (g : (J → ℂ) → ℝ) (f : K → (J → ℂ) → ℝ) (c : K → ℝ)
    (hg : ContDiffAt ℝ 2 g z) (hf : ∀ k, ContDiffAt ℝ 2 (f k) z) (w : J → ℂ) (s : Finset K) :
    ContDiffAt ℝ 2 (fun y => g y + ∑ k ∈ s, c k * f k y) z ∧
      ReciprocityTheory.AnForm.levi (fun y => g y + ∑ k ∈ s, c k * f k y) z w =
        ReciprocityTheory.AnForm.levi g z w + ∑ k ∈ s, c k * ReciprocityTheory.AnForm.levi (f k) z w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«TorusInvariantLevi».«levi_add_sum» := P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_levi_add_sum_b89c89512e17
