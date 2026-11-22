-- Prove2me | Theorems.Thm_Replay_minReplay_unique
-- name    : Replay.minReplay_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:05:48.134293+00:00
-- url     : https://prove2.me/theorems/5f79adcf-305d-4305-b24d-3a3265c40209
-- title:
--   Replay: min Replay unique
-- statement:
--   The Replay construction uses the min Replay unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Replay.lean#L39-L42
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Replay.lean#L39-L42

import Definitions.Def_EventStructures_Family_Log
import Definitions.Def_EventStructures_Family_Replay
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)
open Replay
local infixl:50 " ⊨ " => Log.compatibleWithLog F R

theorem Replay.minReplay_unique {l : Set F.Event} {σ₁ σ₂ : Computations F}
    (h₁ : isMinReplay F R l σ₁) (h₂ : isMinReplay F R l σ₂) :
    conf F σ₁ = conf F σ₂ := by sorry
