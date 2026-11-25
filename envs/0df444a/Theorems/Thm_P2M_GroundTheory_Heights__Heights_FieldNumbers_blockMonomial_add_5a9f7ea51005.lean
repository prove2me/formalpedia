-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_blockMonomial_add_5a9f7ea51005
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_blockMonomial_add_5a9f7ea51005
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:53.856196+00:00
-- url     : https://prove2.me/theorems/c3e8099e-dec0-41bf-b527-8b4a61f74278
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers block Monomial add 5a9f7ea51005: P2 M Ground Theory Heights  Heights Field Numbers block Monomial add 5a9f7ea51005
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers block Monomial add 5a9f7ea51005 construction uses the P2 M Ground Theory Heights  Heights Field Numbers block Monomial add 5a9f7ea51005 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBase.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PIntNumBase.lean#L37-L39

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
omit [DecidableEq K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_blockMonomial_add_5a9f7ea51005 (i : ∀ k, ι k) (m n : K → ℕ) :
    blockMonomial (F := F) i (m + n) = blockMonomial i m * blockMonomial i n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«blockMonomial_add» := P2M_GroundTheory_Heights__Heights_FieldNumbers_blockMonomial_add_5a9f7ea51005
