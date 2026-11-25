-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_rpow_identity_846bbc1944ac
-- name    : P2M_GroundTheory_Heights__Theta_projectiveLineClassData_rpow_identity_846bbc1944ac
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:55:01.188596+00:00
-- url     : https://prove2.me/theorems/d2eb514f-0348-4604-bb48-513fa8a7fc1c
-- title:
--   P2 M Ground Theory Heights  Theta projective Line Class Data rpow identity 846bbc1944ac: P2 M Ground Theory Heights  Theta projective Line Class Data rpow identity 846bbc1944ac
-- statement:
--   The P2 M Ground Theory Heights  Theta projective Line Class Data rpow identity 846bbc1944ac construction uses the P2 M Ground Theory Heights  Theta projective Line Class Data rpow identity 846bbc1944ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean#L265-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean#L265-L272

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
variable {K : Type} [Field K] [NumberField K]
open FractionalIdeal EtaPeriodLatticeClass
local notation "↑ᶠ" J => ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)

theorem P2M_GroundTheory_Heights__Theta_projectiveLineClassData_rpow_identity_846bbc1944ac {n q y : ℝ} (hn : 0 < n) (hq : 0 < q) (hy : 0 < y) (s : ℝ) :
    (n ^ 2 * q / (2 * y)) ^ (-s) = (2 / q) ^ s * (y ^ s / n ^ (2 * s)) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«projectiveLineClassData».«rpow_identity» := P2M_GroundTheory_Heights__Theta_projectiveLineClassData_rpow_identity_846bbc1944ac
