-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_mem_two_invDiff_iff_7e97d9b4234b
-- name    : P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_mem_two_invDiff_iff_7e97d9b4234b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:08:02.646833+00:00
-- url     : https://prove2.me/theorems/325f40d6-84ff-4dff-81f5-b987b2cc4e8c
-- title:
--   P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf mem two inv Diff iff 7e97d9b4234b: P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf mem two inv Diff iff 7e97d9b4234b
-- statement:
--   The P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf mem two inv Diff iff 7e97d9b4234b construction uses the P2 M Ground Theory Heights  Theta Unitary Reduction Dual Hom Pf mem two inv Diff iff 7e97d9b4234b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L103-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearFormEqZeroOfIntegers.lean#L103-L129

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_UnitaryReduction_UnipotentRadicalPlaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearFormEqZeroOfIntegers
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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.UnitaryReduction
open GroundTheory.Heights₂.Theta.UnitaryReduction.DualHomPf
open NumberField Module FunctionalEquationAlt FunctionalEquationAlt.MetSpace NumberField.InfinitePlace
open scoped InnerProductSpace nonZeroDivisors ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_mem_two_invDiff_iff_7e97d9b4234b (t : E) :
    t ∈ FractionalIdeal.spanSingleton (𝓞 E)⁰ (2 : E) * invDiff E ↔
      ∀ c : 𝓞 E, ∃ n : ℤ, Algebra.trace ℚ E ((c : E) * t) = 2 * n := by sorry

alias «GroundTheory».«Heights₂».«Theta».«UnitaryReduction».«DualHomPf».«mem_two_invDiff_iff» := P2M_GroundTheory_Heights__Theta_UnitaryReduction_DualHomPf_mem_two_invDiff_iff_7e97d9b4234b
