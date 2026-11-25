-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_regLine_8cd27babf8cd
-- name    : P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_regLine_8cd27babf8cd
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:19:39.344636+00:00
-- url     : https://prove2.me/theorems/6ad22fc3-1c85-5403-9568-b74ad7661dc8
-- title:
--   P2 M Ground Theory Heights  Heights Inter is Smooth Herm reg Line 8cd27babf8cd: P2 M Ground Theory Heights  Heights Inter is Smooth Herm reg Line 8cd27babf8cd
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter is Smooth Herm reg Line 8cd27babf8cd construction uses the P2 M Ground Theory Heights  Heights Inter is Smooth Herm reg Line 8cd27babf8cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegLine.lean#L71-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegLine.lean#L71-L84

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

theorem P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_regLine_8cd27babf8cd (hE : IsSmoothHerm E) (hε : 0 < ε) : IsSmoothHerm (regLine E t ht ε) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«isSmoothHerm_regLine» := P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_regLine_8cd27babf8cd
