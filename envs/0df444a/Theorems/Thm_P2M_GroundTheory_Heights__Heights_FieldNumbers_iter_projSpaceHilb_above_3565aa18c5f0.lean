-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_above_3565aa18c5f0
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_above_3565aa18c5f0
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:40.923379+00:00
-- url     : https://prove2.me/theorems/41480984-8bc6-4982-b850-e5f612dba564
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers iter proj Space Hilb above 3565aa18c5f0: P2 M Ground Theory Heights  Heights Field Numbers iter proj Space Hilb above 3565aa18c5f0
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers iter proj Space Hilb above 3565aa18c5f0 construction uses the P2 M Ground Theory Heights  Heights Field Numbers iter proj Space Hilb above 3565aa18c5f0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L152-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L152-L157

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPNProduct
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_above_3565aa18c5f0 (N j : ℕ) (hj : N < j) (t : ℤ) (ht : (j : ℤ) ≤ t) :
    diff1^[j] (projSpaceHilb N) t = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«iter_projSpaceHilb_above» := P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_above_3565aa18c5f0
