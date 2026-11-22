-- Prove2me | Theorems.Thm_Replay_maxReplay_unique_config
-- name    : Replay.maxReplay_unique_config
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:56:33.366633+00:00
-- url     : https://prove2.me/theorems/80d206d0-c382-4b81-bb1f-e770a43baf44
-- title:
--   Replay: max Replay unique config
-- statement:
--   The Replay construction uses the max Replay unique config property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Replay.lean#L34-L37
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Replay.lean#L34-L37

import Definitions.Def_EventStructures_Family_Log
import Definitions.Def_EventStructures_Family_Replay
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)
open Replay
local infixl:50 " ⊨ " => Log.compatibleWithLog F R

theorem Replay.maxReplay_unique_config {l : Set F.Event} {σ₁ σ₂ : Computations F}
    (h₁ : isMaxReplay F R l σ₁) (h₂ : isMaxReplay F R l σ₂) :
    (conf F σ₁).1 = (conf F σ₂).1 := by sorry
