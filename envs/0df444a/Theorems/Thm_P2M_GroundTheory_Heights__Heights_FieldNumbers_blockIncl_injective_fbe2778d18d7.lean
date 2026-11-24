-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_blockIncl_injective_fbe2778d18d7
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_blockIncl_injective_fbe2778d18d7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:31.697778+00:00
-- url     : https://prove2.me/theorems/6b916b6e-0730-494b-ad70-70b6482ae080
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers block Incl injective fbe2778d18d7: P2 M Ground Theory Heights  Heights Field Numbers block Incl injective fbe2778d18d7
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers block Incl injective fbe2778d18d7 construction uses the P2 M Ground Theory Heights  Heights Field Numbers block Incl injective fbe2778d18d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L122-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L122-L128

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_blockIncl_injective_fbe2778d18d7 {K K' : Type*} (j : K ↪ K') (ι' : K' → Type*) :
    Function.Injective (blockIncl j ι') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«blockIncl_injective» := P2M_GroundTheory_Heights__Heights_FieldNumbers_blockIncl_injective_fbe2778d18d7
