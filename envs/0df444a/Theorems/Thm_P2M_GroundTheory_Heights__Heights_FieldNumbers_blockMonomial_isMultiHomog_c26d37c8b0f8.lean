-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_blockMonomial_isMultiHomog_c26d37c8b0f8
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_blockMonomial_isMultiHomog_c26d37c8b0f8
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:56.736255+00:00
-- url     : https://prove2.me/theorems/8e5a087c-a333-5105-9479-ef37f0b3f75c
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers block Monomial is Multi Homog c26d37c8b0f8: P2 M Ground Theory Heights  Heights Field Numbers block Monomial is Multi Homog c26d37c8b0f8
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers block Monomial is Multi Homog c26d37c8b0f8 construction uses the P2 M Ground Theory Heights  Heights Field Numbers block Monomial is Multi Homog c26d37c8b0f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBase.lean#L24-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBase.lean#L24-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBase
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
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_blockMonomial_isMultiHomog_c26d37c8b0f8 (i : ∀ k, ι k) (m : K → ℕ) :
    IsMultiHomog (blockMonomial (F := F) i m) m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«blockMonomial_isMultiHomog» := P2M_GroundTheory_Heights__Heights_FieldNumbers_blockMonomial_isMultiHomog_c26d37c8b0f8
