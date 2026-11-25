-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_6d540496c75a
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_6d540496c75a
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:05.739319+00:00
-- url     : https://prove2.me/theorems/8089c93a-17d3-5f1f-9784-9bf5304a55b2
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers iter proj Space Hilb 6d540496c75a: P2 M Ground Theory Heights  Heights Field Numbers iter proj Space Hilb 6d540496c75a
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers iter proj Space Hilb 6d540496c75a construction uses the P2 M Ground Theory Heights  Heights Field Numbers iter proj Space Hilb 6d540496c75a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L107-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L107-L123

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_6d540496c75a (N : ℕ) : ∀ j : ℕ, j ≤ N → ∀ s : ℕ,
    diff1^[j] (projSpaceHilb N) ((s : ℤ) + j) = (((s + N).choose (N - j) : ℕ) : ℤ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«iter_projSpaceHilb» := P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_6d540496c75a
