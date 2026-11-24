-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_tendsto_sub_const_atTop_5936cf0d3c49
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_tendsto_sub_const_atTop_5936cf0d3c49
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:12.260866+00:00
-- url     : https://prove2.me/theorems/d1c5a00a-6abf-4009-a9d6-4a00e5fb5ab3
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers tendsto sub const at Top 5936cf0d3c49: P2 M Ground Theory Heights  Heights Field Numbers tendsto sub const at Top 5936cf0d3c49
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers tendsto sub const at Top 5936cf0d3c49 construction uses the P2 M Ground Theory Heights  Heights Field Numbers tendsto sub const at Top 5936cf0d3c49 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumAdd.lean#L54-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumAdd.lean#L54-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumAdd
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
open GroundTheory.Heights₂.Heights.NumbersDVR
universe u
variable {K : Type*}

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_tendsto_sub_const_atTop_5936cf0d3c49 (b : K → ℤ) :
    Filter.Tendsto (fun m : K → ℤ => m - b) Filter.atTop Filter.atTop := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«tendsto_sub_const_atTop» := P2M_GroundTheory_Heights__Heights_FieldNumbers_tendsto_sub_const_atTop_5936cf0d3c49
