-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_normSq_mul_det_2844130a5510
-- name    : P2M_GroundTheory_Heights__Theta_projectiveLineClassData_normSq_mul_det_2844130a5510
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:54:38.93638+00:00
-- url     : https://prove2.me/theorems/d2c319a3-ffd0-4e5d-afc5-477020c09fb8
-- title:
--   P2 M Ground Theory Heights  Theta projective Line Class Data norm Sq mul det 2844130a5510: P2 M Ground Theory Heights  Theta projective Line Class Data norm Sq mul det 2844130a5510
-- statement:
--   The P2 M Ground Theory Heights  Theta projective Line Class Data norm Sq mul det 2844130a5510 construction uses the P2 M Ground Theory Heights  Theta projective Line Class Data norm Sq mul det 2844130a5510 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DiscrNegAndAbsNormMul.lean#L108-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DiscrNegAndAbsNormMul.lean#L108-L120

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

theorem P2M_GroundTheory_Heights__Theta_projectiveLineClassData_normSq_mul_det_2844130a5510 (c a b τ : ℂ) (ha : c * a = 1) (hb : c * b = τ) :
    ((‖c‖ ^ 2 : ℝ) : ℂ) * (a * (starRingEnd ℂ) b - (starRingEnd ℂ) a * b) =
      -(2 * τ.im * Complex.I) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«projectiveLineClassData».«normSq_mul_det» := P2M_GroundTheory_Heights__Theta_projectiveLineClassData_normSq_mul_det_2844130a5510
