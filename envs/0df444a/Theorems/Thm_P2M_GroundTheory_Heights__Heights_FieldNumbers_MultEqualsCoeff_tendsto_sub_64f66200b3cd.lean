-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_tendsto_sub_64f66200b3cd
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_tendsto_sub_64f66200b3cd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:04.67766+00:00
-- url     : https://prove2.me/theorems/095c43ef-f00b-48a8-9fdf-73762f17a229
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff tendsto sub 64f66200b3cd: P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff tendsto sub 64f66200b3cd
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff tendsto sub 64f66200b3cd construction uses the P2 M Ground Theory Heights  Heights Field Numbers Mult Equals Coeff tendsto sub 64f66200b3cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMultEqualsCoeff.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PMultEqualsCoeff.lean#L16-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMultEqualsCoeff
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
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.MultEqualsCoeff
variable {K : Type*}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_tendsto_sub_64f66200b3cd (c : K → ℤ) : Tendsto (fun m : K → ℤ => m - c) atTop atTop := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«MultEqualsCoeff».«tendsto_sub» := P2M_GroundTheory_Heights__Heights_FieldNumbers_MultEqualsCoeff_tendsto_sub_64f66200b3cd
