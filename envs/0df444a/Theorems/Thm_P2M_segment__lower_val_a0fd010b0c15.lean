-- Prove2me | Theorems.Thm_P2M_segment__lower_val_a0fd010b0c15
-- name    : P2M_segment__lower_val_a0fd010b0c15
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:24:05.970054+00:00
-- url     : https://prove2.me/theorems/75baa9eb-b017-4c50-870a-abdd32fe57cb
-- title:
--   P2 M segment  lower val a0fd010b0c15: P2 M segment  lower val a0fd010b0c15
-- statement:
--   The P2 M segment  lower val a0fd010b0c15 construction uses the P2 M segment  lower val a0fd010b0c15 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L202-L206
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L202-L206

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
set_option autoImplicit true
open Function Set
variable {φ : ℕ → ℕ}

theorem P2M_segment__lower_val_a0fd010b0c15 (hm : StrictMono φ) {m k : ℕ}
    (hl : φ m ≤ k) : m ≤ Segment' φ k := by sorry

alias «segment'_lower_val» := P2M_segment__lower_val_a0fd010b0c15
