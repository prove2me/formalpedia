-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_natCast_withBot_withTop_eb5b1b957aeb
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_natCast_withBot_withTop_eb5b1b957aeb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:26.379096+00:00
-- url     : https://prove2.me/theorems/be8bea82-a590-4797-b453-8f21126089a3
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted nat Cast with Bot with Top eb5b1b957aeb: P2 M Ground Theory Heights  Heights Field Numbers PFContracted nat Cast with Bot with Top eb5b1b
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted nat Cast with Bot with Top eb5b1b957aeb construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted nat Cast with Bot with Top eb5b1b957aeb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L168-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L168-L169

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
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
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_natCast_withBot_withTop_eb5b1b957aeb (n : ℕ) :
    ((n : ℕ) : WithBot (WithTop ℤ)) = (((n : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«natCast_withBot_withTop» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_natCast_withBot_withTop_eb5b1b957aeb
