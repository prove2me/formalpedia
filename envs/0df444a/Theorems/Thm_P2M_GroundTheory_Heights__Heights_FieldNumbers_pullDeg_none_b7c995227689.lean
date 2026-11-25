-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_none_b7c995227689
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_none_b7c995227689
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:18:53.863807+00:00
-- url     : https://prove2.me/theorems/2b3c7029-3d3a-55f6-8f4d-7b12f51e6626
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers pull Deg none b7c995227689: P2 M Ground Theory Heights  Heights Field Numbers pull Deg none b7c995227689
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers pull Deg none b7c995227689 construction uses the P2 M Ground Theory Heights  Heights Field Numbers pull Deg none b7c995227689 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L29-L34

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_none_b7c995227689 (c : K → ℤ) : pullDeg Function.Embedding.some c none = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«pullDeg_none» := P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_none_b7c995227689
