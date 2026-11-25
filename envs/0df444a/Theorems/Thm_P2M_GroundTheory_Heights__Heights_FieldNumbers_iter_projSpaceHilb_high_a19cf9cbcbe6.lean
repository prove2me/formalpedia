-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_high_a19cf9cbcbe6
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_high_a19cf9cbcbe6
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:17:48.376913+00:00
-- url     : https://prove2.me/theorems/b4669567-4be6-46ea-955d-431a61b17bbf
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers iter proj Space Hilb high a19cf9cbcbe6: P2 M Ground Theory Heights  Heights Field Numbers iter proj Space Hilb high a19cf9cbcbe6
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers iter proj Space Hilb high a19cf9cbcbe6 construction uses the P2 M Ground Theory Heights  Heights Field Numbers iter proj Space Hilb high a19cf9cbcbe6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L135-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPNProduct.lean#L135-L150

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

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_high_a19cf9cbcbe6 (N : ℕ) : ∀ i s : ℕ,
    diff1^[N + 1 + i] (projSpaceHilb N) ((s : ℤ) + ((N + 1 + i : ℕ) : ℤ)) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«iter_projSpaceHilb_high» := P2M_GroundTheory_Heights__Heights_FieldNumbers_iter_projSpaceHilb_high_a19cf9cbcbe6
