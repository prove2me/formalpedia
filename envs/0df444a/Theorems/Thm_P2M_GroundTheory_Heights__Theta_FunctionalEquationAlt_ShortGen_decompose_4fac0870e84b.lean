-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_decompose_4fac0870e84b
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_decompose_4fac0870e84b
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:10:40.066875+00:00
-- url     : https://prove2.me/theorems/d3b0dd3a-5813-5a09-8bd4-ed2880f59083
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen decompose 4fac0870e84b: P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen decompose 4fac0870e84b
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen decompose 4fac0870e84b construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen decompose 4fac0870e84b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L239-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L239-L331

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
open Module Submodule Matrix
open scoped RealInnerProductSpace
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_decompose_4fac0870e84b {m : ℕ} (b : Fin (m + 1) → W) (hb : LinearIndependent ℝ b) {lam : ℝ}
    (hlam : 0 < lam) (hsep : Sep (span ℤ (Set.range b)) lam) :
    ∃ (v : W) (c : Fin m → W), v ∈ span ℤ (Set.range b) ∧ v ≠ 0 ∧ lam ≤ ‖v‖ ∧
      (∀ x ∈ span ℤ (Set.range b), x ≠ 0 → ‖v‖ ≤ ‖x‖) ∧ LinearIndependent ℝ c ∧
      (∀ u, u ∈ span ℤ (Set.range c) ↔ ∃ x ∈ span ℤ (Set.range b), proj v x = u) ∧
      Sep (span ℤ (Set.range c)) (lam / 2) ∧
      (gram ℝ b).det = ‖v‖ ^ 2 * (gram ℝ c).det := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«ShortGen».«decompose» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_decompose_4fac0870e84b
