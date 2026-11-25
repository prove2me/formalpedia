-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_bounds_a050c0d6526e
-- name    : P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_bounds_a050c0d6526e
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:34:24.496623+00:00
-- url     : https://prove2.me/theorems/3c009fd5-489b-49b0-a7e6-f54f06175506
-- title:
--   P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen bounds a050c0d6526e: P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen bounds a050c0d6526e
-- statement:
--   The P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen bounds a050c0d6526e construction uses the P2 M Ground Theory Heights  Theta Functional Equation Alt Short Gen bounds a050c0d6526e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L333-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/LinearIndependentRealOfInt.lean#L333-L402

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

theorem P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_bounds_a050c0d6526e (m : ℕ) :
    (∀ lam : ℝ, 0 < lam → ∃ g : ℝ, 0 < g ∧ ∀ b : Fin m → W, LinearIndependent ℝ b →
        Sep (span ℤ (Set.range b)) lam → g ≤ (gram ℝ b).det) ∧
    (∀ lam : ℝ, 0 < lam → ∀ C : ℝ, ∃ R : ℝ, ∀ b : Fin m → W, LinearIndependent ℝ b →
        Sep (span ℤ (Set.range b)) lam → (gram ℝ b).det ≤ C →
        span ℤ (Set.range b) ≤ span ℤ {x | x ∈ span ℤ (Set.range b) ∧ ‖x‖ ≤ R}) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FunctionalEquationAlt».«ShortGen».«bounds» := P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_bounds_a050c0d6526e
