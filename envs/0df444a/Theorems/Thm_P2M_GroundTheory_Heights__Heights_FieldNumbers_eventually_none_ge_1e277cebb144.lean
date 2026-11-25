-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_eventually_none_ge_1e277cebb144
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_eventually_none_ge_1e277cebb144
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:50.90991+00:00
-- url     : https://prove2.me/theorems/99316a9b-1258-430f-a754-b16253883562
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers eventually none ge 1e277cebb144: P2 M Ground Theory Heights  Heights Field Numbers eventually none ge 1e277cebb144
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers eventually none ge 1e277cebb144 construction uses the P2 M Ground Theory Heights  Heights Field Numbers eventually none ge 1e277cebb144 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L92-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L92-L93

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_eventually_none_ge_1e277cebb144 (a : ℤ) : ∀ᶠ m : Option K → ℤ in atTop, a ≤ m none := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«eventually_none_ge» := P2M_GroundTheory_Heights__Heights_FieldNumbers_eventually_none_ge_1e277cebb144
