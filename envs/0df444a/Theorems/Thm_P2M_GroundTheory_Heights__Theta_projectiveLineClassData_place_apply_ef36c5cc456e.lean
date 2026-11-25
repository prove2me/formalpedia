-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_place_apply_ef36c5cc456e
-- name    : P2M_GroundTheory_Heights__Theta_projectiveLineClassData_place_apply_ef36c5cc456e
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:54:15.369063+00:00
-- url     : https://prove2.me/theorems/6cbcf1dd-7230-493b-9636-929d79c10f23
-- title:
--   P2 M Ground Theory Heights  Theta projective Line Class Data place apply ef36c5cc456e: P2 M Ground Theory Heights  Theta projective Line Class Data place apply ef36c5cc456e
-- statement:
--   The P2 M Ground Theory Heights  Theta projective Line Class Data place apply ef36c5cc456e construction uses the P2 M Ground Theory Heights  Theta projective Line Class Data place apply ef36c5cc456e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DiscrNegAndAbsNormMul.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DiscrNegAndAbsNormMul.lean#L45-L47

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

theorem P2M_GroundTheory_Heights__Theta_projectiveLineClassData_place_apply_ef36c5cc456e (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (w : InfinitePlace K) (x : K) : w x = ‖σ x‖ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«projectiveLineClassData».«place_apply» := P2M_GroundTheory_Heights__Theta_projectiveLineClassData_place_apply_ef36c5cc456e
