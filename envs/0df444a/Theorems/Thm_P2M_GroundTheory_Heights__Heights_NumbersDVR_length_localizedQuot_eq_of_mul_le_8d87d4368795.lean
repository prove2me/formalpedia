-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedQuot_eq_of_mul_le_8d87d4368795
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedQuot_eq_of_mul_le_8d87d4368795
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:11:32.14902+00:00
-- url     : https://prove2.me/theorems/f2c8c65c-babb-4fd6-a79c-13bce05a1fdf
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR length localized Quot eq of mul le 8d87d4368795: P2 M Ground Theory Heights  Heights Numbers DVR length localized Quot eq of mul le 8d87d4368795
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR length localized Quot eq of mul le 8d87d4368795 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR length localized Quot eq of mul le 8d87d4368795 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinVertDivIff.lean#L22-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinVertDivIff.lean#L22-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsMoreFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PCutByForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemMinimalPrimesOfDivCycleNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinVertDivIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {A : Type*} [CommRing A]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedQuot_eq_of_mul_le_8d87d4368795 {I J W : Ideal A} [W.IsPrime] (hIJ : I ≤ J) {s : A}
    (hs : s ∉ W) (hsJ : ∀ x ∈ J, s * x ∈ I) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ I)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ J)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«length_localizedQuot_eq_of_mul_le» := P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedQuot_eq_of_mul_le_8d87d4368795
