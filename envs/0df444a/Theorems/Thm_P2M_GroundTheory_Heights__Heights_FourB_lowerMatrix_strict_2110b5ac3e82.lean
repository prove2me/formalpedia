-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_lowerMatrix_strict_2110b5ac3e82
-- name    : P2M_GroundTheory_Heights__Heights_FourB_lowerMatrix_strict_2110b5ac3e82
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:40:18.525773+00:00
-- url     : https://prove2.me/theorems/0b17e580-a482-4809-b387-88b8fe439df9
-- title:
--   P2 M Ground Theory Heights  Heights Four B lower Matrix strict 2110b5ac3e82: P2 M Ground Theory Heights  Heights Four B lower Matrix strict 2110b5ac3e82
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B lower Matrix strict 2110b5ac3e82 construction uses the P2 M Ground Theory Heights  Heights Four B lower Matrix strict 2110b5ac3e82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsDeriv.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsDeriv.lean#L13-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsDeriv
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
open Polynomial Matrix
noncomputable section
variable {N : ℕ} (p i : ℕ) (hi : i ≤ N)

theorem P2M_GroundTheory_Heights__Heights_FourB_lowerMatrix_strict_2110b5ac3e82 (u : LowerPair N → ℂ) :
    ∀ a b : Fin N, ¬ b < a → lowerMatrix u a b = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«lowerMatrix_strict» := P2M_GroundTheory_Heights__Heights_FourB_lowerMatrix_strict_2110b5ac3e82
