-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_realEisenstein_eq_tsum_1d2f5bf29f0e
-- name    : P2M_GroundTheory_Heights__Theta_projectiveLineClassData_realEisenstein_eq_tsum_1d2f5bf29f0e
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:55:21.612517+00:00
-- url     : https://prove2.me/theorems/29914081-e723-4cfc-8468-ea839516ad28
-- title:
--   P2 M Ground Theory Heights  Theta projective Line Class Data real Eisenstein eq tsum 1d2f5bf29f0e: P2 M Ground Theory Heights  Theta projective Line Class Data real Eisenstein eq tsum 1d2f5bf29f0e
-- statement:
--   The P2 M Ground Theory Heights  Theta projective Line Class Data real Eisenstein eq tsum 1d2f5bf29f0e construction uses the P2 M Ground Theory Heights  Theta projective Line Class Data real Eisenstein eq tsum 1d2f5bf29f0e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean#L20-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean#L20-L20

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

theorem P2M_GroundTheory_Heights__Theta_projectiveLineClassData_realEisenstein_eq_tsum_1d2f5bf29f0e (τ : ℍ) (s : ℝ) : realEisenstein τ s = ∑' p, eisTerm τ s p := by sorry

alias «GroundTheory».«Heights₂».«Theta».«projectiveLineClassData».«realEisenstein_eq_tsum» := P2M_GroundTheory_Heights__Theta_projectiveLineClassData_realEisenstein_eq_tsum_1d2f5bf29f0e
