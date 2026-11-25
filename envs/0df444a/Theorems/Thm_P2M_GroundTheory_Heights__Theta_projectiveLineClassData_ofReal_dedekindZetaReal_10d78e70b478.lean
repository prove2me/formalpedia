-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_ofReal_dedekindZetaReal_10d78e70b478
-- name    : P2M_GroundTheory_Heights__Theta_projectiveLineClassData_ofReal_dedekindZetaReal_10d78e70b478
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:54:43.012588+00:00
-- url     : https://prove2.me/theorems/763f97ce-250e-4744-bfcf-076d56b1cafc
-- title:
--   P2 M Ground Theory Heights  Theta projective Line Class Data of Real dedekind Zeta Real 10d78e70b478: P2 M Ground Theory Heights  Theta projective Line Class Data of Real dedekind Zeta Real 10d78e70b4
-- statement:
--   The P2 M Ground Theory Heights  Theta projective Line Class Data of Real dedekind Zeta Real 10d78e70b478 construction uses the P2 M Ground Theory Heights  Theta projective Line Class Data of Real dedekind Zeta Real 10d78e70b478 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean#L49-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean#L49-L65

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
variable (K : Type) [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Theta_projectiveLineClassData_ofReal_dedekindZetaReal_10d78e70b478 {s : ℝ} (hs : 1 < s) :
    ENNReal.ofReal (GroundTheory.Global.dedekindZetaReal K s) =
      ∑' I : Ideal (𝓞 K), ENNReal.ofReal ((Ideal.absNorm I : ℝ) ^ (-s)) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«projectiveLineClassData».«ofReal_dedekindZetaReal» := P2M_GroundTheory_Heights__Theta_projectiveLineClassData_ofReal_dedekindZetaReal_10d78e70b478
