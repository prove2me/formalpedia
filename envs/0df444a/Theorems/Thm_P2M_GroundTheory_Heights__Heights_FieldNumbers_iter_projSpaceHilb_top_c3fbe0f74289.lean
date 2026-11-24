-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_top_c3fbe0f74289
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_top_c3fbe0f74289
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:34.990051+00:00
-- url     : https://prove2.me/theorems/fd05cc06-88f0-40f8-8fd9-0d58915102c0
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers iter proj Space Hilb top c3fbe0f74289: P2 M Ground Theory Heights  Heights Field Numbers iter proj Space Hilb top c3fbe0f74289
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers iter proj Space Hilb top c3fbe0f74289 construction uses the P2 M Ground Theory Heights  Heights Field Numbers iter proj Space Hilb top c3fbe0f74289 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L130-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L130-L133

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_top_c3fbe0f74289 (N : ℕ) (t : ℤ) (ht : (N : ℤ) ≤ t) :
    diff1^[N] (projSpaceHilb N) t = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«iter_projSpaceHilb_top» := P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_top_c3fbe0f74289
