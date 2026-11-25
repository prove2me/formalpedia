-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_tendsto_restrict_2aee757d54c1
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_tendsto_restrict_2aee757d54c1
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:19.838949+00:00
-- url     : https://prove2.me/theorems/83f294a5-01c2-5bd9-9e43-fadc1be6c683
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers tendsto restrict 2aee757d54c1: P2 M Ground Theory Heights  Heights Field Numbers tendsto restrict 2aee757d54c1
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers tendsto restrict 2aee757d54c1 construction uses the P2 M Ground Theory Heights  Heights Field Numbers tendsto restrict 2aee757d54c1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L88-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L88-L90

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_tendsto_restrict_2aee757d54c1 :
    Tendsto (fun m : Option K → ℤ => fun k => m (some k)) atTop atTop := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«tendsto_restrict» := P2M_GroundTheory_Heights__Heights_FieldNumbers_tendsto_restrict_2aee757d54c1
