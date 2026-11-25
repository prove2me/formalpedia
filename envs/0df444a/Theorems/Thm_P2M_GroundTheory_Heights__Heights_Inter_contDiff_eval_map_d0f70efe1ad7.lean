-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_contDiff_eval_map_d0f70efe1ad7
-- name    : P2M_GroundTheory_Heights__Heights_Inter_contDiff_eval_map_d0f70efe1ad7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:42.56672+00:00
-- url     : https://prove2.me/theorems/06e914c0-e639-4e98-9f0c-bf6df5d559ab
-- title:
--   P2 M Ground Theory Heights  Heights Inter cont Diff eval map d0f70efe1ad7: P2 M Ground Theory Heights  Heights Inter cont Diff eval map d0f70efe1ad7
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter cont Diff eval map d0f70efe1ad7 construction uses the P2 M Ground Theory Heights  Heights Inter cont Diff eval map d0f70efe1ad7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegLine.lean#L64-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegLine.lean#L64-L69

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegLine
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {E : HermLine ι} {t : MRing ι} {ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a}
  {ε : ℝ}

theorem P2M_GroundTheory_Heights__Heights_Inter_contDiff_eval_map_d0f70efe1ad7 (t : MRing ι) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => eval z (map (Int.castRingHom ℂ) t)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«contDiff_eval_map» := P2M_GroundTheory_Heights__Heights_Inter_contDiff_eval_map_d0f70efe1ad7
