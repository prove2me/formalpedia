-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_eventualValue_eq_zero_9297a58f17ee
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_eventualValue_eq_zero_9297a58f17ee
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:37.088128+00:00
-- url     : https://prove2.me/theorems/c4495813-a052-52b0-8cbf-6482f5de83f3
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers PFContracted eventual Value eq zero 9297a58f17ee: P2 M Ground Theory Heights  Heights Field Numbers PFContracted eventual Value eq zero 9297a58f17ee
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers PFContracted eventual Value eq zero 9297a58f17ee construction uses the P2 M Ground Theory Heights  Heights Field Numbers PFContracted eventual Value eq zero 9297a58f17ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L206-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean#L206-L212

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_eventualValue_eq_zero_9297a58f17ee {K : Type*} {f : (K → ℤ) → ℤ}
    (h : ∀ᶠ m in Filter.atTop, f m = 0) : eventualValue f = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PFContracted».«eventualValue_eq_zero» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_eventualValue_eq_zero_9297a58f17ee
