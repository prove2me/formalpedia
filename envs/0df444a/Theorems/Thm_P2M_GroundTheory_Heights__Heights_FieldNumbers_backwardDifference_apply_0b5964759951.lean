-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_backwardDifference_apply_0b5964759951
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_backwardDifference_apply_0b5964759951
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:39.821+00:00
-- url     : https://prove2.me/theorems/0ea177ae-65fc-4e2f-9b0a-70ccb662a63a
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers backward Difference apply 0b5964759951: P2 M Ground Theory Heights  Heights Field Numbers backward Difference apply 0b5964759951
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers backward Difference apply 0b5964759951 construction uses the P2 M Ground Theory Heights  Heights Field Numbers backward Difference apply 0b5964759951 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L23-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L23-L23

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
variable {K : Type}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_backwardDifference_apply_0b5964759951 (g : ℤ → ℤ) (t : ℤ) : diff1 g t = g t - g (t - 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«backwardDifference_apply» := P2M_GroundTheory_Heights__Heights_FieldNumbers_backwardDifference_apply_0b5964759951
