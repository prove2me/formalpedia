-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsNear_pow_card_le_norm_prod_4142eeda9e0d
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsNear_pow_card_le_norm_prod_4142eeda9e0d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:10.814797+00:00
-- url     : https://prove2.me/theorems/39abef57-f965-46d7-9238-82f187be6fca
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Roots Near pow card le norm prod 4142eeda9e0d: P2 M Ground Theory Heights  Heights Hilbert Samuel Roots Near pow card le norm prod 4142eeda9e0d
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Roots Near pow card le norm prod 4142eeda9e0d construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Roots Near pow card le norm prod 4142eeda9e0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PRootsNear.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PRootsNear.lean#L9-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootsNear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRootsNear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Filter Topology

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsNear_pow_card_le_norm_prod_4142eeda9e0d (s : Multiset ℂ) (t₀ : ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ a ∈ s, ε ≤ dist a t₀) :
    ε ^ Multiset.card s ≤ ‖(s.map fun a => t₀ - a).prod‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«RootsNear».«pow_card_le_norm_prod» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootsNear_pow_card_le_norm_prod_4142eeda9e0d
