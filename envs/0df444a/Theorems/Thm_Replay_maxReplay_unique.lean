-- Prove2me | Theorems.Thm_Replay_maxReplay_unique
-- name    : Replay.maxReplay_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:05:57.814273+00:00
-- url     : https://prove2.me/theorems/c350854e-84da-4ae1-99d3-39fd2540be35
-- title:
--   Replay: max Replay unique
-- statement:
--   The Replay construction uses the max Replay unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Replay.lean#L44-L47
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Replay.lean#L44-L47

import Definitions.Def_EventStructures_Family_Log
import Definitions.Def_EventStructures_Family_Replay
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)
open Replay
local infixl:50 " ⊨ " => Log.compatibleWithLog F R

theorem Replay.maxReplay_unique {l : Set F.Event} {σ₁ σ₂ : Computations F}
    (h₁ : isMaxReplay F R l σ₁) (h₂ : isMaxReplay F R l σ₂) :
    conf F σ₁ = conf F σ₂ := by sorry
