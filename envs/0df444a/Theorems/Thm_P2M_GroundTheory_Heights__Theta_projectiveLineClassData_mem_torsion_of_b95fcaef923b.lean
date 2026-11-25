-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_mem_torsion_of_b95fcaef923b
-- name    : P2M_GroundTheory_Heights__Theta_projectiveLineClassData_mem_torsion_of_b95fcaef923b
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:54:12.390214+00:00
-- url     : https://prove2.me/theorems/1e7fa0ef-adc2-4186-9e69-9b3a4bcf06d8
-- title:
--   P2 M Ground Theory Heights  Theta projective Line Class Data mem torsion of b95fcaef923b: P2 M Ground Theory Heights  Theta projective Line Class Data mem torsion of b95fcaef923b
-- statement:
--   The P2 M Ground Theory Heights  Theta projective Line Class Data mem torsion of b95fcaef923b construction uses the P2 M Ground Theory Heights  Theta projective Line Class Data mem torsion of b95fcaef923b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DiscrNegAndAbsNormMul.lean#L66-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DiscrNegAndAbsNormMul.lean#L66-L74

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

theorem P2M_GroundTheory_Heights__Theta_projectiveLineClassData_mem_torsion_of_b95fcaef923b (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (u : (𝓞 K)ˣ) : u ∈ Units.torsion K := by sorry

alias «GroundTheory».«Heights₂».«Theta».«projectiveLineClassData».«mem_torsion_of» := P2M_GroundTheory_Heights__Theta_projectiveLineClassData_mem_torsion_of_b95fcaef923b
