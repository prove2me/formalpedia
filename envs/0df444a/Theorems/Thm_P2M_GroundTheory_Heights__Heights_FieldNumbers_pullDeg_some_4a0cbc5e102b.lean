-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_some_4a0cbc5e102b
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_some_4a0cbc5e102b
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:17:57.305253+00:00
-- url     : https://prove2.me/theorems/9a9cc43d-9ac1-409d-a3f5-a1808c98f891
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers pull Deg some 4a0cbc5e102b: P2 M Ground Theory Heights  Heights Field Numbers pull Deg some 4a0cbc5e102b
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers pull Deg some 4a0cbc5e102b construction uses the P2 M Ground Theory Heights  Heights Field Numbers pull Deg some 4a0cbc5e102b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L25-L27

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_some_4a0cbc5e102b (c : K → ℤ) (k : K) :
    pullDeg Function.Embedding.some c (some k) = c k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«pullDeg_some» := P2M_GroundTheory_Heights__Heights_FieldNumbers_pullDeg_some_4a0cbc5e102b
