-- Prove2me | Theorems.Thm_TreeStack_mass_oneOn
-- name    : TreeStack.mass_oneOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:06:05.571829+00:00
-- url     : https://prove2.me/theorems/6bdd4e24-3d6b-42e9-b300-cc6d1492dfe4
-- title:
--   Tree Stack: mass one On
-- statement:
--   The Tree Stack construction uses the mass one On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/PebblingMove.lean#L80-L83
-- source:
--   https://github.com/jfairfaxball-348/TreeStack-Structural-Certificates-for-Stacking-on-Trees/blob/457b88b785e50a749710108a935a661a9d992348/TreeStack/PebblingMove.lean#L80-L83

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_PebblingMove
set_option autoImplicit false
open TreeStack

theorem TreeStack.mass_oneOn {V : Type*} [Fintype V] [DecidableEq V] (s : Finset V) :
    mass (oneOn s) = s.card := by sorry
