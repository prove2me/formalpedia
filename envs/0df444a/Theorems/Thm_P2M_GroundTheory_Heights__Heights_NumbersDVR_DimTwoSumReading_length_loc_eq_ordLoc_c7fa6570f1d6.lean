-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_length_loc_eq_ordLoc_c7fa6570f1d6
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_length_loc_eq_ordLoc_c7fa6570f1d6
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:05:54.130051+00:00
-- url     : https://prove2.me/theorems/0d8fcc7b-d2b8-414f-ab82-12f56220f02c
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Dim Two Sum Reading length loc eq ord Loc c7fa6570f1d6: P2 M Ground Theory Heights  Heights Numbers DVR Dim Two Sum Reading length loc eq ord Loc c7fa65
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Dim Two Sum Reading length loc eq ord Loc c7fa6570f1d6 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Dim Two Sum Reading length loc eq ord Loc c7fa6570f1d6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDimTwoSumReading.lean#L17-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PDimTwoSumReading.lean#L17-L30

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_length_loc_eq_ordLoc_c7fa6570f1d6 (W : Ideal A) [hW : W.IsPrime] (a : A) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (A ⧸ Ideal.span {a})) =
      ordLoc ⟨W, hW⟩ a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«DimTwoSumReading».«length_loc_eq_ordLoc» := P2M_GroundTheory_Heights__Heights_NumbersDVR_DimTwoSumReading_length_loc_eq_ordLoc_c7fa6570f1d6
