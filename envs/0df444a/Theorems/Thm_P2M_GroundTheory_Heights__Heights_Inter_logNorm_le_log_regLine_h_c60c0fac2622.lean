-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_logNorm_le_log_regLine_h_c60c0fac2622
-- name    : P2M_GroundTheory_Heights__Heights_Inter_logNorm_le_log_regLine_h_c60c0fac2622
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:19:41.889831+00:00
-- url     : https://prove2.me/theorems/e4054e6e-b659-48fc-b4ed-c6f4af26e728
-- title:
--   P2 M Ground Theory Heights  Heights Inter log Norm le log reg Line h c60c0fac2622: P2 M Ground Theory Heights  Heights Inter log Norm le log reg Line h c60c0fac2622
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter log Norm le log reg Line h c60c0fac2622 construction uses the P2 M Ground Theory Heights  Heights Inter log Norm le log reg Line h c60c0fac2622 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegLine.lean#L86-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/RegLine.lean#L86-L96

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

theorem P2M_GroundTheory_Heights__Heights_Inter_logNorm_le_log_regLine_h_c60c0fac2622 (hε : 0 ≤ ε) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (ht0 : eval z (map (Int.castRingHom ℂ) t) ≠ 0) :
    logNorm E t z ≤ Real.log ((regLine E t ht ε).h z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«logNorm_le_log_regLine_h» := P2M_GroundTheory_Heights__Heights_Inter_logNorm_le_log_regLine_h_c60c0fac2622
