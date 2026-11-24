-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_eq_mk_5796c1fd3e82
-- name    : P2M_GroundTheory_Heights__Theta_projectiveLineClassData_eq_mk_5796c1fd3e82
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:25.941301+00:00
-- url     : https://prove2.me/theorems/511fec7b-26b6-4efb-bf80-093a073b3b72
-- title:
--   P2 M Ground Theory Heights  Theta projective Line Class Data eq mk 5796c1fd3e82: P2 M Ground Theory Heights  Theta projective Line Class Data eq mk 5796c1fd3e82
-- statement:
--   The P2 M Ground Theory Heights  Theta projective Line Class Data eq mk 5796c1fd3e82 construction uses the P2 M Ground Theory Heights  Theta projective Line Class Data eq mk 5796c1fd3e82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DiscrNegAndAbsNormMul.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DiscrNegAndAbsNormMul.lean#L39-L43

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

theorem P2M_GroundTheory_Heights__Theta_projectiveLineClassData_eq_mk_5796c1fd3e82 (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    (w : InfinitePlace K) : w = mk σ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«projectiveLineClassData».«eq_mk» := P2M_GroundTheory_Heights__Theta_projectiveLineClassData_eq_mk_5796c1fd3e82
