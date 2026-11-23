-- Prove2me | Theorems.Thm_P2M_segment__range_val_15118bfaea7b
-- name    : P2M_segment__range_val_15118bfaea7b
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:33:54.126809+00:00
-- url     : https://prove2.me/theorems/86833dc8-984a-4db7-8ea9-c8ed27768e49
-- title:
--   P2 M segment  range val 15118bfaea7b: P2 M segment  range val 15118bfaea7b
-- statement:
--   The P2 M segment  range val 15118bfaea7b construction uses the P2 M segment  range val 15118bfaea7b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L192-L200
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L192-L200

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
set_option autoImplicit true
open Function Set
variable {φ : ℕ → ℕ}

theorem P2M_segment__range_val_15118bfaea7b (hm : StrictMono φ) {m k : ℕ}
    (hl : φ m ≤ k) (hu : k < φ (m + 1)) : Segment' φ k = m := by sorry

alias «segment'_range_val» := P2M_segment__range_val_15118bfaea7b
