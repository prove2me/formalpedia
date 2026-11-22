-- Prove2me | Theorems.Thm_Replay_minReplay_unique_config
-- name    : Replay.minReplay_unique_config
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T20:56:30.213616+00:00
-- url     : https://prove2.me/theorems/7f964bc1-88e8-40ca-8298-fbc341348f77
-- title:
--   Replay: min Replay unique config
-- statement:
--   The Replay construction uses the min Replay unique config property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Replay.lean#L29-L32
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Replay.lean#L29-L32

import Definitions.Def_EventStructures_Family_Log
import Definitions.Def_EventStructures_Family_Replay
set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L) (R : F.Event → F.Event → Prop)
open Replay
local infixl:50 " ⊨ " => Log.compatibleWithLog F R

theorem Replay.minReplay_unique_config {l : Set F.Event} {σ₁ σ₂ : Computations F}
    (h₁ : isMinReplay F R l σ₁) (h₂ : isMinReplay F R l σ₂) :
    (conf F σ₁).1 = (conf F σ₂).1 := by sorry
