-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_pull_f207d38574a0
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_pull_f207d38574a0
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:21:28.456996+00:00
-- url     : https://prove2.me/theorems/72c23214-7db6-42ba-af28-4ae3ad5bf7c8
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers foldr pull f207d38574a0: P2 M Ground Theory Heights  Heights Field Numbers foldr pull f207d38574a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers foldr pull f207d38574a0 construction uses the P2 M Ground Theory Heights  Heights Field Numbers foldr pull f207d38574a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L61-L66

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_pull_f207d38574a0 (L : List (K → ℤ)) (A : (K → ℤ) → ℤ) (B : ℤ → ℤ) :
    (L.map (pullDeg Function.Embedding.some)).foldr diffStep (prodFn A B) =
      prodFn (L.foldr diffStep A) B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«foldr_pull» := P2M_GroundTheory_Heights__Heights_FieldNumbers_foldr_pull_f207d38574a0
