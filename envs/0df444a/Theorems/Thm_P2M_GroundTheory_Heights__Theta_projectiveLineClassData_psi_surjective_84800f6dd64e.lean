-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_projectiveLineClassData_psi_surjective_84800f6dd64e
-- name    : P2M_GroundTheory_Heights__Theta_projectiveLineClassData_psi_surjective_84800f6dd64e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:54:55.697231+00:00
-- url     : https://prove2.me/theorems/ac883f4f-1117-4f3e-a936-33f9ef761868
-- title:
--   P2 M Ground Theory Heights  Theta projective Line Class Data psi surjective 84800f6dd64e: P2 M Ground Theory Heights  Theta projective Line Class Data psi surjective 84800f6dd64e
-- statement:
--   The P2 M Ground Theory Heights  Theta projective Line Class Data psi surjective 84800f6dd64e construction uses the P2 M Ground Theory Heights  Theta projective Line Class Data psi surjective 84800f6dd64e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean#L153-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean#L153-L184

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

theorem P2M_GroundTheory_Heights__Theta_projectiveLineClassData_psi_surjective_84800f6dd64e (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Function.Surjective (psi J) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«projectiveLineClassData».«psi_surjective» := P2M_GroundTheory_Heights__Theta_projectiveLineClassData_psi_surjective_84800f6dd64e
