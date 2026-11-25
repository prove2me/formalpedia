-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_extend_inj_25c9cbdc37fc
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_extend_inj_25c9cbdc37fc
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:42.629744+00:00
-- url     : https://prove2.me/theorems/87bea52c-cfb0-4877-b195-a681306fd639
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers extend inj 25c9cbdc37fc: P2 M Ground Theory Heights  Heights Field Numbers extend inj 25c9cbdc37fc
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers extend inj 25c9cbdc37fc construction uses the P2 M Ground Theory Heights  Heights Field Numbers extend inj 25c9cbdc37fc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFDegree.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFDegree.lean#L29-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForward
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
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
variable {K K' : Type} (j : K ↪ K') (ι' : K' → Type)

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_extend_inj_25c9cbdc37fc {M : Type*} [Zero M] {b₁ b₂ : K → M} :
    Function.extend j b₁ 0 = Function.extend j b₂ 0 ↔ b₁ = b₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«extend_inj» := P2M_GroundTheory_Heights__Heights_FieldNumbers_extend_inj_25c9cbdc37fc
