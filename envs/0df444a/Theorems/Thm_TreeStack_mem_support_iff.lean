-- Prove2me | Theorems.Thm_TreeStack_mem_support_iff
-- name    : TreeStack.mem_support_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:05:27.240113+00:00
-- url     : https://prove2.me/theorems/7d6e9ff1-4878-500f-91a5-95f4b0bab50e
-- title:
--   Tree Stack: mem support iff
-- statement:
--   The Tree Stack construction uses the mem support iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Basic.lean#L21-L22
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Basic.lean#L21-L22

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Definitions.Def_TreeStack_Basic
set_option autoImplicit false
open TreeStack

theorem TreeStack.mem_support_iff {V : Type*} {C : Configuration V} {v : V} :
    v ∈ support C ↔ 0 < C v := by sorry
