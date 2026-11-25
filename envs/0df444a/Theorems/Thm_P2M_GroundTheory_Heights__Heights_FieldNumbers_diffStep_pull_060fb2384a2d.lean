-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_pull_060fb2384a2d
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_pull_060fb2384a2d
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:49.493811+00:00
-- url     : https://prove2.me/theorems/4ccc4a02-ecf5-493b-9281-7009d6174c84
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers diff Step pull 060fb2384a2d: P2 M Ground Theory Heights  Heights Field Numbers diff Step pull 060fb2384a2d
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers diff Step pull 060fb2384a2d construction uses the P2 M Ground Theory Heights  Heights Field Numbers diff Step pull 060fb2384a2d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L36-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L36-L47

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_pull_060fb2384a2d (c : K → ℤ) (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    diffStep (pullDeg Function.Embedding.some c) (prodFn A B) = prodFn (diffStep c A) B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«diffStep_pull» := P2M_GroundTheory_Heights__Heights_FieldNumbers_diffStep_pull_060fb2384a2d
