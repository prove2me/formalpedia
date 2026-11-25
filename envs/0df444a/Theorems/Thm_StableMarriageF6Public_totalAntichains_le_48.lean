-- Prove2me | Theorems.Thm_StableMarriageF6Public_totalAntichains_le_48
-- name    : StableMarriageF6Public.totalAntichains_le_48
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T13:16:14.678709+00:00
-- url     : https://prove2.me/theorems/c5de0d43-ba9b-4172-b240-d26733a0f6b6
-- title:
--   Stable Marriage F6 Public: total Antichains le 48
-- statement:
--   The Stable Marriage F6 Public construction uses the total Antichains le 48 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/palomar/Solution.lean#L41-L49
-- source:
--   https://github.com/insammael/stable-marriage-f6/blob/2bbce71bd8dedafd31539ed6a7a5cd71b12f50d6/palomar/Solution.lean#L41-L49

import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Definitions.Def_StableMarriageF6_PalomarSolution
import Theorems.Thm_F6ConvexWindow_totalAntichains_le_48

set_option autoImplicit true
noncomputable section
open StableMarriageF6Public
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [PartialOrder V]

theorem StableMarriageF6Public.totalAntichains_le_48
    (hw : widthLE (V := V) 3)
    (hci : ci2 (V := V))
    (hn : Fintype.card V ≤ 15) :
    totalNumberOfAntichains (V := V) ≤ 48 := by sorry
