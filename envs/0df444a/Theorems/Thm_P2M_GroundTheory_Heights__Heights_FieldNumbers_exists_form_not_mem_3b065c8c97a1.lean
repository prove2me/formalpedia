-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_form_not_mem_3b065c8c97a1
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_form_not_mem_3b065c8c97a1
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:54:52.313796+00:00
-- url     : https://prove2.me/theorems/f863934a-460f-47f4-99b5-d5392f2d45b5
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers exists form not mem 3b065c8c97a1: P2 M Ground Theory Heights  Heights Field Numbers exists form not mem 3b065c8c97a1
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers exists form not mem 3b065c8c97a1 construction uses the P2 M Ground Theory Heights  Heights Field Numbers exists form not mem 3b065c8c97a1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDivPushForwardLocal.lean#L18-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PDivPushForwardLocal.lean#L18-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivCycleMinimal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsConeLocalLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocalRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalFiniteRank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalLength
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KrullDimQuotientEqOneIffEqBot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDivPushForwardLocal
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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_form_not_mem_3b065c8c97a1 {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u}
    [Field F] {W : Ideal (MRing ι F)} (hW : IsMultiProjPrime W) (c : K → ℕ) :
    ∃ h : MRing ι F, IsMultiHomog h c ∧ h ∉ W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«exists_form_not_mem» := P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_form_not_mem_3b065c8c97a1
