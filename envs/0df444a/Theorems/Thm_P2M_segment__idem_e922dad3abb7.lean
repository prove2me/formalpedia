-- Prove2me | Theorems.Thm_P2M_segment__idem_e922dad3abb7
-- name    : P2M_segment__idem_e922dad3abb7
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T04:33:47.608799+00:00
-- url     : https://prove2.me/theorems/71806f24-61a1-4f65-9a6d-b56ba589dafd
-- title:
--   P2 M segment  idem e922dad3abb7: P2 M segment  idem e922dad3abb7
-- statement:
--   The P2 M segment  idem e922dad3abb7 construction uses the P2 M segment  idem e922dad3abb7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L187-L190
-- source:
--   https://github.com/ctchou/AutomataTheory/blob/f196548710ce1ba8e7d4aa73b1cf846248ecfcb8/AutomataTheory/Sequences/Segments.lean#L187-L190

import Definitions.Def_AutomataTheory_Sequences_Basic
import Definitions.Def_AutomataTheory_Sequences_Segments
set_option autoImplicit true
open Function Set
variable {φ : ℕ → ℕ}

theorem P2M_segment__idem_e922dad3abb7 (hm : StrictMono φ) (k : ℕ) :
    Segment' φ (φ k) = k := by sorry

alias «segment'_idem» := P2M_segment__idem_e922dad3abb7
