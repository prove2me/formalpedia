-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_dedekindZeta_eq_sum_realEisenstein_899175d53bfe
-- name    : P2M_GroundTheory_Heights__Theta_projectiveLineClassData_dedekindZeta_eq_sum_realEisenstein_899175d53bfe
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:44:05.354718+00:00
-- url     : https://prove2.me/theorems/ffd89bba-9838-401a-a145-7b3ea4c88f40
-- title:
--   P2 M Ground Theory Heights  Theta projective Line Class Data dedekind Zeta eq sum real Eisenstein 899175d53bfe: P2 M Ground Theory Heights  Theta projective Line Class Data dedekind Zeta eq sum real E
-- statement:
--   The P2 M Ground Theory Heights  Theta projective Line Class Data dedekind Zeta eq sum real Eisenstein 899175d53bfe construction uses the P2 M Ground Theory Heights  Theta projective Line Class Data dedekind Zeta eq sum real Eisenstein 899175d53bfe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean#L384-L436
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean#L384-L436

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DedekindZetaEqSumRealEisenstein
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.projectiveLineClassData
open NumberField UpperHalfPlane
open scoped nonZeroDivisors

theorem P2M_GroundTheory_Heights__Theta_projectiveLineClassData_dedekindZeta_eq_sum_realEisenstein_899175d53bfe {K : Type} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (τ : ClassGroup (𝓞 K) → ℍ)
    (hτ : ∀ A, ∃ I : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ClassGroup.mk K I = A ∧
      IsLatticeParam (σ '' ((I : FractionalIdeal (𝓞 K)⁰ K) : Set K)) (τ A))
    {s : ℝ} (hs : 1 < s) :
    NumberField.dedekindZeta K s =
      (((NumberField.Units.torsionOrder K : ℝ)⁻¹ * (2 / Real.sqrt |(NumberField.discr K : ℝ)|) ^ s *
        ∑ A : ClassGroup (𝓞 K), realEisenstein (τ A) s : ℝ) : ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«projectiveLineClassData».«dedekindZeta_eq_sum_realEisenstein» := P2M_GroundTheory_Heights__Theta_projectiveLineClassData_dedekindZeta_eq_sum_realEisenstein_899175d53bfe
