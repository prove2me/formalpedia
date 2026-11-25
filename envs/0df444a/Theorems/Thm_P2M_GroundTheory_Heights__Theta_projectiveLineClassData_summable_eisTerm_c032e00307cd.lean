-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_summable_eisTerm_c032e00307cd
-- name    : P2M_GroundTheory_Heights__Theta_projectiveLineClassData_summable_eisTerm_c032e00307cd
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:55:13.531003+00:00
-- url     : https://prove2.me/theorems/a703eb67-1507-4f96-b52b-dad054bfe923
-- title:
--   P2 M Ground Theory Heights  Theta projective Line Class Data summable eis Term c032e00307cd: P2 M Ground Theory Heights  Theta projective Line Class Data summable eis Term c032e00307cd
-- statement:
--   The P2 M Ground Theory Heights  Theta projective Line Class Data summable eis Term c032e00307cd construction uses the P2 M Ground Theory Heights  Theta projective Line Class Data summable eis Term c032e00307cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean#L28-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean#L28-L41

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

theorem P2M_GroundTheory_Heights__Theta_projectiveLineClassData_summable_eisTerm_c032e00307cd (τ : ℍ) {s : ℝ} (hs : 1 < s) : Summable (eisTerm τ s) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«projectiveLineClassData».«summable_eisTerm» := P2M_GroundTheory_Heights__Theta_projectiveLineClassData_summable_eisTerm_c032e00307cd
