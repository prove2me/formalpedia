-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_homFracDegZero_of_mem_degZeroLoc_d64725dd4b85
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_homFracDegZero_of_mem_degZeroLoc_d64725dd4b85
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:39:11.422176+00:00
-- url     : https://prove2.me/theorems/2aca4263-0b18-5af7-8e26-518518ed2cd2
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers mem hom Frac Deg Zero of mem deg Zero Loc d64725dd4b85: P2 M Ground Theory Heights  Heights Field Numbers mem hom Frac Deg Zero of mem deg Zero Loc d6
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers mem hom Frac Deg Zero of mem deg Zero Loc d64725dd4b85 construction uses the P2 M Ground Theory Heights  Heights Field Numbers mem hom Frac Deg Zero of mem deg Zero Loc d64725dd4b85 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalFiniteRank.lean#L55-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PSemilocalFiniteRank.lean#L55-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFibreFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalFiniteRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_homFracDegZero_of_mem_degZeroLoc_d64725dd4b85 {K : Type*} [DecidableEq K] {ι : K → Type*}
    {F : Type*} [Field F] (P : Ideal (MRing ι F)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι F))) :
    ∀ x ∈ degZeroLoc P 𝒲, x ∈ homFracDegZero P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«mem_homFracDegZero_of_mem_degZeroLoc» := P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_homFracDegZero_of_mem_degZeroLoc_d64725dd4b85
