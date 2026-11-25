-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_eq_monomial_of_isMultiHomog_point_043f9fbc675f
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_eq_monomial_of_isMultiHomog_point_043f9fbc675f
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:14.937627+00:00
-- url     : https://prove2.me/theorems/aaf627ca-b329-4c10-9433-c51c8c42d010
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers eq monomial of is Multi Homog point 043f9fbc675f: P2 M Ground Theory Heights  Heights Field Numbers eq monomial of is Multi Homog point 043f9fbc675f
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers eq monomial of is Multi Homog point 043f9fbc675f construction uses the P2 M Ground Theory Heights  Heights Field Numbers eq monomial of is Multi Homog point 043f9fbc675f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L258-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L258-L276

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_eq_monomial_of_isMultiHomog_point_043f9fbc675f {F : Type*} [Field F] (f : MRing (ProjIdx 0) F)
    (b : Unit → ℕ) (hf : IsMultiHomog f b) :
    f = monomial (Finsupp.single ⟨(), 0⟩ (b ())) (coeff (Finsupp.single ⟨(), 0⟩ (b ())) f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«eq_monomial_of_isMultiHomog_point» := P2M_GroundTheory_Heights__Heights_FieldNumbers_eq_monomial_of_isMultiHomog_point_043f9fbc675f
