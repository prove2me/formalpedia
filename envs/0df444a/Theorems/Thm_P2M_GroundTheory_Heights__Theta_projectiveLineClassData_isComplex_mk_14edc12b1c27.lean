-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_isComplex_mk_14edc12b1c27
-- name    : P2M_GroundTheory_Heights__Theta_projectiveLineClassData_isComplex_mk_14edc12b1c27
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:54:16.885805+00:00
-- url     : https://prove2.me/theorems/da844109-dd5a-45e9-893a-00b8e382af34
-- title:
--   P2 M Ground Theory Heights  Theta projective Line Class Data is Complex mk 14edc12b1c27: P2 M Ground Theory Heights  Theta projective Line Class Data is Complex mk 14edc12b1c27
-- statement:
--   The P2 M Ground Theory Heights  Theta projective Line Class Data is Complex mk 14edc12b1c27 construction uses the P2 M Ground Theory Heights  Theta projective Line Class Data is Complex mk 14edc12b1c27 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DiscrNegAndAbsNormMul.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DiscrNegAndAbsNormMul.lean#L51-L52

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
omit [NumberField K]

theorem P2M_GroundTheory_Heights__Theta_projectiveLineClassData_isComplex_mk_14edc12b1c27 (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0) : IsComplex (mk σ) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«projectiveLineClassData».«isComplex_mk» := P2M_GroundTheory_Heights__Theta_projectiveLineClassData_isComplex_mk_14edc12b1c27
