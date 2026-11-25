-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_length_max_eq_ordMod_f57d7a15dfe9
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_length_max_eq_ordMod_f57d7a15dfe9
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:11:23.508798+00:00
-- url     : https://prove2.me/theorems/74cb4e29-258b-5d9c-b302-47075958aa79
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Dim Two Sum Reading length max eq ord Mod f57d7a15dfe9: P2 M Ground Theory Heights  Heights Numbers DVR Dim Two Sum Reading length max eq ord Mod f57d7a
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Dim Two Sum Reading length max eq ord Mod f57d7a15dfe9 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Dim Two Sum Reading length max eq ord Mod f57d7a15dfe9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDimTwoSumReading.lean#L32-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDimTwoSumReading.lean#L32-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsLocalCoeffLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_SwapLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimTwoSumReading
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
open ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.DimTwoSumReading
variable {A : Type*} [CommRing A]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_length_max_eq_ordMod_f57d7a15dfe9 [IsLocalRing A] (W : Ideal A) [hW : W.IsPrime] (b : A) :
    Module.length (Localization.AtPrime (maximalIdeal A))
        (LocalizedModule (maximalIdeal A).primeCompl (A ⧸ (W ⊔ Ideal.span {b}))) =
      ordMod ⟨W, hW⟩ b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«DimTwoSumReading».«length_max_eq_ordMod» := P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_length_max_eq_ordMod_f57d7a15dfe9
