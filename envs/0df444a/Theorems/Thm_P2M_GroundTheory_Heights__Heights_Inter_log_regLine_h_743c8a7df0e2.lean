-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_log_regLine_h_743c8a7df0e2
-- name    : P2M_GroundTheory_Heights__Heights_Inter_log_regLine_h_743c8a7df0e2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:20:37.058613+00:00
-- url     : https://prove2.me/theorems/a1f1c2a1-8599-4425-97a8-ade74e99dc94
-- title:
--   P2 M Ground Theory Heights  Heights Inter log reg Line h 743c8a7df0e2: P2 M Ground Theory Heights  Heights Inter log reg Line h 743c8a7df0e2
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter log reg Line h 743c8a7df0e2 construction uses the P2 M Ground Theory Heights  Heights Inter log reg Line h 743c8a7df0e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegLine.lean#L60-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegLine.lean#L60-L62

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

theorem P2M_GroundTheory_Heights__Heights_Inter_log_regLine_h_743c8a7df0e2 (z : (Σ k, ι k) → ℂ) :
    Real.log ((regLine E t ht ε).h z) = Real.log (secNorm E t z ^ 2 + ε) / 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«log_regLine_h» := P2M_GroundTheory_Heights__Heights_Inter_log_regLine_h_743c8a7df0e2
