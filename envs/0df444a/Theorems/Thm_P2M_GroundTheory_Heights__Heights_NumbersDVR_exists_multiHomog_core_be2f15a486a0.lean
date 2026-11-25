-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_multiHomog_core_be2f15a486a0
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_multiHomog_core_be2f15a486a0
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:10:53.03583+00:00
-- url     : https://prove2.me/theorems/b7927a48-a704-42d1-a1ef-7e44bb0e9e81
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR exists multi Homog core be2f15a486a0: P2 M Ground Theory Heights  Heights Numbers DVR exists multi Homog core be2f15a486a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR exists multi Homog core be2f15a486a0 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR exists multi Homog core be2f15a486a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinVertDivIff.lean#L100-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PTwinVertDivIff.lean#L100-L119

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
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_multiHomog_core_be2f15a486a0 {W : Ideal (MRing ι R)} (hW : W.IsPrime) :
    ∃ W' : Ideal (MRing ι R), W'.IsPrime ∧ IsMultiHomogIdeal W' ∧ W' ≤ W ∧
      (∀ J : Ideal (MRing ι R), IsMultiHomogIdeal J → J ≤ W → J ≤ W') ∧
      (∀ (x : MRing ι R) (γ : K → ℕ), IsMultiHomog x γ → x ∈ W → x ∈ W') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«exists_multiHomog_core» := P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_multiHomog_core_be2f15a486a0
