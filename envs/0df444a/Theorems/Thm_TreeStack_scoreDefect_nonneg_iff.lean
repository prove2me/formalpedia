-- Prove2me | Theorems.Thm_TreeStack_scoreDefect_nonneg_iff
-- name    : TreeStack.scoreDefect_nonneg_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:46:34.084469+00:00
-- url     : https://prove2.me/theorems/b112acaa-386d-59cb-b586-368f2abe616a
-- title:
--   Tree Stack: score Defect nonneg iff
-- statement:
--   The Tree Stack construction uses the score Defect nonneg iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Defect.lean#L181-L185
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/Defect.lean#L181-L185

import Mathlib
import Definitions.Def_TreeStack_Obstruction
import Definitions.Def_TreeStack_Defect
set_option autoImplicit false
open TreeStack

theorem TreeStack.scoreDefect_nonneg_iff
    {V : Type*} [Fintype V]
    (T : FiniteTree V) (C : Configuration V) (v : V) :
    0 ≤ scoreDefect T C v ↔ score T C v ≤ 0 := by sorry
