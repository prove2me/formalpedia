-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_discr_neg_and_absNorm_mul_efde573e849a
-- name    : P2M_GroundTheory_Heights__Theta_projectiveLineClassData_discr_neg_and_absNorm_mul_efde573e849a
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:54:54.005835+00:00
-- url     : https://prove2.me/theorems/aab11270-f46d-4e53-8044-05ac3e75b567
-- title:
--   P2 M Ground Theory Heights  Theta projective Line Class Data discr neg and abs Norm mul efde573e849a: P2 M Ground Theory Heights  Theta projective Line Class Data discr neg and abs Norm mul efde573e84
-- statement:
--   The P2 M Ground Theory Heights  Theta projective Line Class Data discr neg and abs Norm mul efde573e849a construction uses the P2 M Ground Theory Heights  Theta projective Line Class Data discr neg and abs Norm mul efde573e849a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DiscrNegAndAbsNormMul.lean#L128-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DiscrNegAndAbsNormMul.lean#L128-L240

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_RealEisensteinNonneg
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaPeriodLatticeClassPf
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
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
open NumberField NumberField.InfinitePlace NumberField.ComplexEmbedding UpperHalfPlane
open scoped nonZeroDivisors ComplexConjugate
variable {K : Type} [Field K] [NumberField K]
open EtaPeriodLatticeClass

theorem P2M_GroundTheory_Heights__Theta_projectiveLineClassData_discr_neg_and_absNorm_mul_efde573e849a (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ)
    (hσ : ∃ x : K, (σ x).im ≠ 0) (I : FractionalIdeal (𝓞 K)⁰ K) (τ : ℍ) (c : ℂ) (hc : c ≠ 0)
    (himg : (fun z => c * z) '' (σ '' (I : Set K)) = latticeOf (τ : ℂ)) :
    (discr K : ℝ) < 0 ∧
      ((FractionalIdeal.absNorm I : ℚ) : ℝ) * ‖c‖ ^ 2 = 2 * τ.im / Real.sqrt |(discr K : ℝ)| := by sorry

alias «GroundTheory».«Heights₂».«Theta».«projectiveLineClassData».«discr_neg_and_absNorm_mul» := P2M_GroundTheory_Heights__Theta_projectiveLineClassData_discr_neg_and_absNorm_mul_efde573e849a
