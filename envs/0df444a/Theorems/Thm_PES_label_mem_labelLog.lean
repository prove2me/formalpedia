-- Prove2me | Theorems.Thm_PES_label_mem_labelLog
-- name    : PES.label_mem_labelLog
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:07:16.925806+00:00
-- url     : https://prove2.me/theorems/197ba9d2-ae35-4ca9-a829-862f952b5038
-- title:
--   PES: label mem label Log
-- statement:
--   The PES construction uses the label mem label Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Log.lean#L69-L71
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Prime/Log.lean#L69-L71

import Definitions.Def_EventStructures_Prime_Configuration
import Definitions.Def_EventStructures_Family_Log
import Definitions.Def_EventStructures_Prime_Log
import Theorems.Thm_Log_label_mem_labelLog

set_option autoImplicit true
variable {L : Type*} (es : PES L)
open PES
open Configuration
local infixl:50 " ## " => es.minimalConflict
open PES

theorem PES.label_mem_labelLog {c : Conf es} {e : es.Event} (h : e ∈ log es c) :
    es.label e ∈ labelLog es c := by sorry
