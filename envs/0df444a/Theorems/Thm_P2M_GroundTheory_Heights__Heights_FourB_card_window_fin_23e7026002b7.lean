-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_card_window_fin_23e7026002b7
-- name    : P2M_GroundTheory_Heights__Heights_FourB_card_window_fin_23e7026002b7
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:34:03.585692+00:00
-- url     : https://prove2.me/theorems/41bb0b04-e422-5f67-a1cb-8e3b60d399c9
-- title:
--   P2 M Ground Theory Heights  Heights Four B card window fin 23e7026002b7: P2 M Ground Theory Heights  Heights Four B card window fin 23e7026002b7
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B card window fin 23e7026002b7 construction uses the P2 M Ground Theory Heights  Heights Four B card window fin 23e7026002b7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PRhoBound.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PRhoBound.lean#L9-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PRhoBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open Finset

theorem P2M_GroundTheory_Heights__Heights_FourB_card_window_fin_23e7026002b7 (n a b : ℕ) (hb : b ≤ n) :
    ∑ i : Fin n, (if a ≤ i.val ∧ i.val < b then (1 : ℝ) else 0) = ((b - a : ℕ) : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«card_window_fin» := P2M_GroundTheory_Heights__Heights_FourB_card_window_fin_23e7026002b7
