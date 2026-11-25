-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_natCard_units_ca5c537aacec
-- name    : P2M_GroundTheory_Heights__Theta_projectiveLineClassData_natCard_units_ca5c537aacec
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:54:09.052254+00:00
-- url     : https://prove2.me/theorems/9399aca6-846f-4ea5-883d-f1be269dfede
-- title:
--   P2 M Ground Theory Heights  Theta projective Line Class Data nat Card units ca5c537aacec: P2 M Ground Theory Heights  Theta projective Line Class Data nat Card units ca5c537aacec
-- statement:
--   The P2 M Ground Theory Heights  Theta projective Line Class Data nat Card units ca5c537aacec construction uses the P2 M Ground Theory Heights  Theta projective Line Class Data nat Card units ca5c537aacec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DiscrNegAndAbsNormMul.lean#L76-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DiscrNegAndAbsNormMul.lean#L76-L79

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

theorem P2M_GroundTheory_Heights__Theta_projectiveLineClassData_natCard_units_ca5c537aacec (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0) :
    Nat.card (𝓞 K)ˣ = Units.torsionOrder K := by sorry

alias «GroundTheory».«Heights₂».«Theta».«projectiveLineClassData».«natCard_units» := P2M_GroundTheory_Heights__Theta_projectiveLineClassData_natCard_units_ca5c537aacec
