-- Prove2me | Theorems.Thm_TreeStack_no_step_oneOn
-- name    : TreeStack.no_step_oneOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:06:44.623111+00:00
-- url     : https://prove2.me/theorems/7fad59ce-7773-4f24-b21b-603ddf5cf48b
-- title:
--   Tree Stack: no step one On
-- statement:
--   The Tree Stack construction uses the no step one On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/PebblingMove.lean#L85-L88
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/PebblingMove.lean#L85-L88

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_PebblingMove
set_option autoImplicit false
open TreeStack

theorem TreeStack.no_step_oneOn {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (s : Finset V) {D : Configuration V} : ¬ PebbleStep G (oneOn s) D := by sorry
